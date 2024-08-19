// SPDX-License-Identifier: GPL-2.0

//! Red-black trees.
//!
//! C header: [`include/linux/rbtree.h`](srctree/include/linux/rbtree.h)
//!
//! Reference: <https://www.kernel.org/doc/html/latest/core-api/rbtree.html>

use crate::{alloc::Flags, bindings, container_of, error::Result, prelude::*};
use alloc::boxed::Box;
use core::{
    cmp::{Ord, Ordering},
    marker::PhantomData,
    mem::MaybeUninit,
    ptr::{addr_of_mut, from_mut, NonNull},
};

/// A red-black tree with owned nodes.
///
/// It is backed by the kernel C red-black trees.
///
/// # Examples
///
/// In the example below we do several operations on a tree. We note that insertions may fail if
/// the system is out of memory.
///
/// ```
/// use kernel::{alloc::flags, rbtree::{RBTree, RBTreeNode, RBTreeNodeReservation}};
///
/// // Create a new tree.
/// let mut tree = RBTree::new();
///
/// // Insert three elements.
/// tree.try_create_and_insert(20, 200, flags::GFP_KERNEL)?;
/// tree.try_create_and_insert(10, 100, flags::GFP_KERNEL)?;
/// tree.try_create_and_insert(30, 300, flags::GFP_KERNEL)?;
///
/// // Check the nodes we just inserted.
/// {
///     assert_eq!(tree.get(&10).unwrap(), &100);
///     assert_eq!(tree.get(&20).unwrap(), &200);
///     assert_eq!(tree.get(&30).unwrap(), &300);
/// }
///
/// // Iterate over the nodes we just inserted.
/// {
///     let mut iter = tree.iter();
///     assert_eq!(iter.next().unwrap(), (&10, &100));
///     assert_eq!(iter.next().unwrap(), (&20, &200));
///     assert_eq!(iter.next().unwrap(), (&30, &300));
///     assert!(iter.next().is_none());
/// }
///
/// // Print all elements.
/// for (key, value) in &tree {
///     pr_info!("{} = {}\n", key, value);
/// }
///
/// // Replace one of the elements.
/// tree.try_create_and_insert(10, 1000, flags::GFP_KERNEL)?;
///
/// // Check that the tree reflects the replacement.
/// {
///     let mut iter = tree.iter();
///     assert_eq!(iter.next().unwrap(), (&10, &1000));
///     assert_eq!(iter.next().unwrap(), (&20, &200));
///     assert_eq!(iter.next().unwrap(), (&30, &300));
///     assert!(iter.next().is_none());
/// }
///
/// // Change the value of one of the elements.
/// *tree.get_mut(&30).unwrap() = 3000;
///
/// // Check that the tree reflects the update.
/// {
///     let mut iter = tree.iter();
///     assert_eq!(iter.next().unwrap(), (&10, &1000));
///     assert_eq!(iter.next().unwrap(), (&20, &200));
///     assert_eq!(iter.next().unwrap(), (&30, &3000));
///     assert!(iter.next().is_none());
/// }
///
/// // Remove an element.
/// tree.remove(&10);
///
/// // Check that the tree reflects the removal.
/// {
///     let mut iter = tree.iter();
///     assert_eq!(iter.next().unwrap(), (&20, &200));
///     assert_eq!(iter.next().unwrap(), (&30, &3000));
///     assert!(iter.next().is_none());
/// }
///
/// # Ok::<(), Error>(())
/// ```
///
/// In the example below, we first allocate a node, acquire a spinlock, then insert the node into
/// the tree. This is useful when the insertion context does not allow sleeping, for example, when
/// holding a spinlock.
///
/// ```
/// use kernel::{alloc::flags, rbtree::{RBTree, RBTreeNode}, sync::SpinLock};
///
/// fn insert_test(tree: &SpinLock<RBTree<u32, u32>>) -> Result {
///     // Pre-allocate node. This may fail (as it allocates memory).
///     let node = RBTreeNode::new(10, 100, flags::GFP_KERNEL)?;
///
///     // Insert node while holding the lock. It is guaranteed to succeed with no allocation
///     // attempts.
///     let mut guard = tree.lock();
///     guard.insert(node);
///     Ok(())
/// }
/// ```
///
/// In the example below, we reuse an existing node allocation from an element we removed.
///
/// ```
/// use kernel::{alloc::flags, rbtree::{RBTree, RBTreeNodeReservation}};
///
/// // Create a new tree.
/// let mut tree = RBTree::new();
///
/// // Insert three elements.
/// tree.try_create_and_insert(20, 200, flags::GFP_KERNEL)?;
/// tree.try_create_and_insert(10, 100, flags::GFP_KERNEL)?;
/// tree.try_create_and_insert(30, 300, flags::GFP_KERNEL)?;
///
/// // Check the nodes we just inserted.
/// {
///     let mut iter = tree.iter();
///     assert_eq!(iter.next().unwrap(), (&10, &100));
///     assert_eq!(iter.next().unwrap(), (&20, &200));
///     assert_eq!(iter.next().unwrap(), (&30, &300));
///     assert!(iter.next().is_none());
/// }
///
/// // Remove a node, getting back ownership of it.
/// let existing = tree.remove(&30).unwrap();
///
/// // Check that the tree reflects the removal.
/// {
///     let mut iter = tree.iter();
///     assert_eq!(iter.next().unwrap(), (&10, &100));
///     assert_eq!(iter.next().unwrap(), (&20, &200));
///     assert!(iter.next().is_none());
/// }
///
/// // Create a preallocated reservation that we can re-use later.
/// let reservation = RBTreeNodeReservation::new(flags::GFP_KERNEL)?;
///
/// // Insert a new node into the tree, reusing the previous allocation. This is guaranteed to
/// // succeed (no memory allocations).
/// tree.insert(reservation.into_node(15, 150));
///
/// // Check that the tree reflect the new insertion.
/// {
///     let mut iter = tree.iter();
///     assert_eq!(iter.next().unwrap(), (&10, &100));
///     assert_eq!(iter.next().unwrap(), (&15, &150));
///     assert_eq!(iter.next().unwrap(), (&20, &200));
///     assert!(iter.next().is_none());
/// }
///
/// # Ok::<(), Error>(())
/// ```
///
/// # Invariants
///
/// Non-null parent/children pointers stored in instances of the `rb_node` C struct are always
/// valid, and pointing to a field of our internal representation of a node.
pub struct RBTree<K, V> {
    root: bindings::rb_root,
    _p: PhantomData<Node<K, V>>,
}

// SAFETY: An [`RBTree`] allows the same kinds of access to its values that a struct allows to its
// fields, so we use the same Send condition as would be used for a struct with K and V fields.
unsafe impl<K: Send, V: Send> Send for RBTree<K, V> {}

// SAFETY: An [`RBTree`] allows the same kinds of access to its values that a struct allows to its
// fields, so we use the same Sync condition as would be used for a struct with K and V fields.
unsafe impl<K: Sync, V: Sync> Sync for RBTree<K, V> {}

impl<K, V> RBTree<K, V> {
    /// Creates a new and empty tree.
    pub fn new() -> Self {
        Self {
            // INVARIANT: There are no nodes in the tree, so the invariant holds vacuously.
            root: bindings::rb_root::default(),
            _p: PhantomData,
        }
    }

    /// Returns an iterator over the tree nodes, sorted by key.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            _tree: PhantomData,
            // INVARIANT:
            //   - `self.root` is a valid pointer to a tree root.
            //   - `bindings::rb_first` produces a valid pointer to a node given `root` is valid.
            iter_raw: IterRaw {
                // SAFETY: by the invariants, all pointers are valid.
                next: unsafe { bindings::rb_first(&self.root) },
                _phantom: PhantomData,
            },
        }
    }

    /// Returns a mutable iterator over the tree nodes, sorted by key.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            _tree: PhantomData,
            // INVARIANT:
            //   - `self.root` is a valid pointer to a tree root.
            //   - `bindings::rb_first` produces a valid pointer to a node given `root` is valid.
            iter_raw: IterRaw {
                // SAFETY: by the invariants, all pointers are valid.
                next: unsafe { bindings::rb_first(from_mut(&mut self.root)) },
                _phantom: PhantomData,
            },
        }
    }

    /// Returns an iterator over the keys of the nodes in the tree, in sorted order.
    pub fn keys(&self) -> impl Iterator<Item = &'_ K> {
        self.iter().map(|(k, _)| k)
    }

    /// Returns an iterator over the values of the nodes in the tree, sorted by key.
    pub fn values(&self) -> impl Iterator<Item = &'_ V> {
        self.iter().map(|(_, v)| v)
    }

    /// Returns a mutable iterator over the values of the nodes in the tree, sorted by key.
    pub fn values_mut(&mut self) -> impl Iterator<Item = &'_ mut V> {
        self.iter_mut().map(|(_, v)| v)
    }
}

impl<K, V> RBTree<K, V>
where
    K: Ord,
{
    /// Tries to insert a new value into the tree.
    ///
    /// It overwrites a node if one already exists with the same key and returns it (containing the
    /// key/value pair). Returns [`None`] if a node with the same key didn't already exist.
    ///
    /// Returns an error if it cannot allocate memory for the new node.
    pub fn try_create_and_insert(
        &mut self,
        key: K,
        value: V,
        flags: Flags,
    ) -> Result<Option<RBTreeNode<K, V>>> {
        Ok(self.insert(RBTreeNode::new(key, value, flags)?))
    }

    /// Inserts a new node into the tree.
    ///
    /// It overwrites a node if one already exists with the same key and returns it (containing the
    /// key/value pair). Returns [`None`] if a node with the same key didn't already exist.
    ///
    /// This function always succeeds.
    pub fn insert(&mut self, RBTreeNode { node }: RBTreeNode<K, V>) -> Option<RBTreeNode<K, V>> {
        let node = Box::into_raw(node);
        // SAFETY: `node` is valid at least until we call `Box::from_raw`, which only happens when
        // the node is removed or replaced.
        let node_links = unsafe { addr_of_mut!((*node).links) };

        // The parameters of `bindings::rb_link_node` are as follows:
        // - `node`: A pointer to an uninitialized node being inserted.
        // - `parent`: A pointer to an existing node in the tree. One of its child pointers must be
        //          null, and `node` will become a child of `parent` by replacing that child pointer
        //          with a pointer to `node`.
        // - `rb_link`: A pointer to either the left-child or right-child field of `parent`. This
        //          specifies which child of `parent` should hold `node` after this call. The
        //          value of `*rb_link` must be null before the call to `rb_link_node`. If the
        //          red/black tree is empty, then it’s also possible for `parent` to be null. In
        //          this case, `rb_link` is a pointer to the `root` field of the red/black tree.
        //
        // We will traverse the tree looking for a node that has a null pointer as its child,
        // representing an empty subtree where we can insert our new node. We need to make sure
        // that we preserve the ordering of the nodes in the tree. In each iteration of the loop
        // we store `parent` and `child_field_of_parent`, and the new `node` will go somewhere
        // in the subtree of `parent` that `child_field_of_parent` points at. Once
        // we find an empty subtree, we can insert the new node using `rb_link_node`.
        let mut parent = core::ptr::null_mut();
        let mut child_field_of_parent: &mut *mut bindings::rb_node = &mut self.root.rb_node;
        while !child_field_of_parent.is_null() {
            parent = *child_field_of_parent;

            // We need to determine whether `node` should be the left or right child of `parent`,
            // so we will compare with the `key` field of `parent` a.k.a. `this` below.
            //
            // SAFETY: By the type invariant of `Self`, all non-null `rb_node` pointers stored in `self`
            // point to the links field of `Node<K, V>` objects.
            let this = unsafe { container_of!(parent, Node<K, V>, links) };

            // SAFETY: `this` is a non-null node so it is valid by the type invariants. `node` is
            // valid until the node is removed.
            match unsafe { (*node).key.cmp(&(*this).key) } {
                // We would like `node` to be the left child of `parent`.  Move to this child to check
                // whether we can use it, or continue searching, at the next iteration.
                //
                // SAFETY: `parent` is a non-null node so it is valid by the type invariants.
                Ordering::Less => child_field_of_parent = unsafe { &mut (*parent).rb_left },
                // We would like `node` to be the right child of `parent`.  Move to this child to check
                // whether we can use it, or continue searching, at the next iteration.
                //
                // SAFETY: `parent` is a non-null node so it is valid by the type invariants.
                Ordering::Greater => child_field_of_parent = unsafe { &mut (*parent).rb_right },
                Ordering::Equal => {
                    // There is an existing node in the tree with this key, and that node is
                    // `parent`. Thus, we are replacing parent with a new node.
                    //
                    // INVARIANT: We are replacing an existing node with a new one, which is valid.
                    // It remains valid because we "forgot" it with `Box::into_raw`.
                    // SAFETY: All pointers are non-null and valid.
                    unsafe { bindings::rb_replace_node(parent, node_links, &mut self.root) };

                    // INVARIANT: The node is being returned and the caller may free it, however,
                    // it was removed from the tree. So the invariants still hold.
                    return Some(RBTreeNode {
                        // SAFETY: `this` was a node in the tree, so it is valid.
                        node: unsafe { Box::from_raw(this.cast_mut()) },
                    });
                }
            }
        }

        // INVARIANT: We are linking in a new node, which is valid. It remains valid because we
        // "forgot" it with `Box::into_raw`.
        // SAFETY: All pointers are non-null and valid (`*child_field_of_parent` is null, but `child_field_of_parent` is a
        // mutable reference).
        unsafe { bindings::rb_link_node(node_links, parent, child_field_of_parent) };

        // SAFETY: All pointers are valid. `node` has just been inserted into the tree.
        unsafe { bindings::rb_insert_color(node_links, &mut self.root) };
        None
    }

    /// Returns a node with the given key, if one exists.
    fn find(&self, key: &K) -> Option<NonNull<Node<K, V>>> {
        let mut node = self.root.rb_node;
        while !node.is_null() {
            // SAFETY: By the type invariant of `Self`, all non-null `rb_node` pointers stored in `self`
            // point to the links field of `Node<K, V>` objects.
            let this = unsafe { container_of!(node, Node<K, V>, links) };
            // SAFETY: `this` is a non-null node so it is valid by the type invariants.
            node = match key.cmp(unsafe { &(*this).key }) {
                // SAFETY: `node` is a non-null node so it is valid by the type invariants.
                Ordering::Less => unsafe { (*node).rb_left },
                // SAFETY: `node` is a non-null node so it is valid by the type invariants.
                Ordering::Greater => unsafe { (*node).rb_right },
                Ordering::Equal => return NonNull::new(this.cast_mut()),
            }
        }
        None
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get(&self, key: &K) -> Option<&V> {
        // SAFETY: The `find` return value is a node in the tree, so it is valid.
        self.find(key).map(|node| unsafe { &node.as_ref().value })
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        // SAFETY: The `find` return value is a node in the tree, so it is valid.
        self.find(key)
            .map(|mut node| unsafe { &mut node.as_mut().value })
    }

    /// Removes the node with the given key from the tree.
    ///
    /// It returns the node that was removed if one exists, or [`None`] otherwise.
    fn remove_node(&mut self, key: &K) -> Option<RBTreeNode<K, V>> {
        let mut node = self.find(key)?;

        // SAFETY: The `find` return value is a node in the tree, so it is valid.
        unsafe { bindings::rb_erase(&mut node.as_mut().links, &mut self.root) };

        // INVARIANT: The node is being returned and the caller may free it, however, it was
        // removed from the tree. So the invariants still hold.
        Some(RBTreeNode {
            // SAFETY: The `find` return value was a node in the tree, so it is valid.
            node: unsafe { Box::from_raw(node.as_ptr()) },
        })
    }

    /// Removes the node with the given key from the tree.
    ///
    /// It returns the value that was removed if one exists, or [`None`] otherwise.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        self.remove_node(key).map(|node| node.node.value)
    }
}

impl<K, V> Default for RBTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Drop for RBTree<K, V> {
    fn drop(&mut self) {
        // SAFETY: `root` is valid as it's embedded in `self` and we have a valid `self`.
        let mut next = unsafe { bindings::rb_first_postorder(&self.root) };

        // INVARIANT: The loop invariant is that all tree nodes from `next` in postorder are valid.
        while !next.is_null() {
            // SAFETY: All links fields we create are in a `Node<K, V>`.
            let this = unsafe { container_of!(next, Node<K, V>, links) };

            // Find out what the next node is before disposing of the current one.
            // SAFETY: `next` and all nodes in postorder are still valid.
            next = unsafe { bindings::rb_next_postorder(next) };

            // INVARIANT: This is the destructor, so we break the type invariant during clean-up,
            // but it is not observable. The loop invariant is still maintained.

            // SAFETY: `this` is valid per the loop invariant.
            unsafe { drop(Box::from_raw(this.cast_mut())) };
        }
    }
}

impl<'a, K, V> IntoIterator for &'a RBTree<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the nodes of a [`RBTree`].
///
/// Instances are created by calling [`RBTree::iter`].
pub struct Iter<'a, K, V> {
    _tree: PhantomData<&'a RBTree<K, V>>,
    iter_raw: IterRaw<K, V>,
}

// SAFETY: The [`Iter`] gives out immutable references to K and V, so it has the same
// thread safety requirements as immutable references.
unsafe impl<'a, K: Sync, V: Sync> Send for Iter<'a, K, V> {}

// SAFETY: The [`Iter`] gives out immutable references to K and V, so it has the same
// thread safety requirements as immutable references.
unsafe impl<'a, K: Sync, V: Sync> Sync for Iter<'a, K, V> {}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: Due to `self._tree`, `k` and `v` are valid for the lifetime of `'a`.
        self.iter_raw.next().map(|(k, v)| unsafe { (&*k, &*v) })
    }
}

impl<'a, K, V> IntoIterator for &'a mut RBTree<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// A mutable iterator over the nodes of a [`RBTree`].
///
/// Instances are created by calling [`RBTree::iter_mut`].
pub struct IterMut<'a, K, V> {
    _tree: PhantomData<&'a mut RBTree<K, V>>,
    iter_raw: IterRaw<K, V>,
}

// SAFETY: The [`IterMut`] has exclusive access to both `K` and `V`, so it is sufficient to require them to be `Send`.
// The iterator only gives out immutable references to the keys, but since the iterator has excusive access to those same
// keys, `Send` is sufficient. `Sync` would be okay, but it is more restrictive to the user.
unsafe impl<'a, K: Send, V: Send> Send for IterMut<'a, K, V> {}

// SAFETY: The [`IterMut`] gives out immutable references to K and mutable references to V, so it has the same
// thread safety requirements as mutable references.
unsafe impl<'a, K: Sync, V: Sync> Sync for IterMut<'a, K, V> {}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_raw.next().map(|(k, v)|
            // SAFETY: Due to `&mut self`, we have exclusive access to `k` and `v`, for the lifetime of `'a`.
            unsafe { (&*k, &mut *v) })
    }
}

/// A raw iterator over the nodes of a [`RBTree`].
///
/// # Invariants
/// - `self.next` is a valid pointer.
/// - `self.next` points to a node stored inside of a valid `RBTree`.
struct IterRaw<K, V> {
    next: *mut bindings::rb_node,
    _phantom: PhantomData<fn() -> (K, V)>,
}

impl<K, V> Iterator for IterRaw<K, V> {
    type Item = (*mut K, *mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.next.is_null() {
            return None;
        }

        // SAFETY: By the type invariant of `IterRaw`, `self.next` is a valid node in an `RBTree`,
        // and by the type invariant of `RBTree`, all nodes point to the links field of `Node<K, V>` objects.
        let cur: *mut Node<K, V> =
            unsafe { container_of!(self.next, Node<K, V>, links) }.cast_mut();

        // SAFETY: `self.next` is a valid tree node by the type invariants.
        self.next = unsafe { bindings::rb_next(self.next) };

        // SAFETY: By the same reasoning above, it is safe to dereference the node.
        Some(unsafe { (addr_of_mut!((*cur).key), addr_of_mut!((*cur).value)) })
    }
}

/// A memory reservation for a red-black tree node.
///
///
/// It contains the memory needed to hold a node that can be inserted into a red-black tree. One
/// can be obtained by directly allocating it ([`RBTreeNodeReservation::new`]).
pub struct RBTreeNodeReservation<K, V> {
    node: Box<MaybeUninit<Node<K, V>>>,
}

impl<K, V> RBTreeNodeReservation<K, V> {
    /// Allocates memory for a node to be eventually initialised and inserted into the tree via a
    /// call to [`RBTree::insert`].
    pub fn new(flags: Flags) -> Result<RBTreeNodeReservation<K, V>> {
        Ok(RBTreeNodeReservation {
            node: <Box<_> as BoxExt<_>>::new_uninit(flags)?,
        })
    }
}

// SAFETY: This doesn't actually contain K or V, and is just a memory allocation. Those can always
// be moved across threads.
unsafe impl<K, V> Send for RBTreeNodeReservation<K, V> {}

// SAFETY: This doesn't actually contain K or V, and is just a memory allocation.
unsafe impl<K, V> Sync for RBTreeNodeReservation<K, V> {}

impl<K, V> RBTreeNodeReservation<K, V> {
    /// Initialises a node reservation.
    ///
    /// It then becomes an [`RBTreeNode`] that can be inserted into a tree.
    pub fn into_node(self, key: K, value: V) -> RBTreeNode<K, V> {
        let node = Box::write(
            self.node,
            Node {
                key,
                value,
                links: bindings::rb_node::default(),
            },
        );
        RBTreeNode { node }
    }
}

/// A red-black tree node.
///
/// The node is fully initialised (with key and value) and can be inserted into a tree without any
/// extra allocations or failure paths.
pub struct RBTreeNode<K, V> {
    node: Box<Node<K, V>>,
}

impl<K, V> RBTreeNode<K, V> {
    /// Allocates and initialises a node that can be inserted into the tree via
    /// [`RBTree::insert`].
    pub fn new(key: K, value: V, flags: Flags) -> Result<RBTreeNode<K, V>> {
        Ok(RBTreeNodeReservation::new(flags)?.into_node(key, value))
    }
}

// SAFETY: If K and V can be sent across threads, then it's also okay to send [`RBTreeNode`] across
// threads.
unsafe impl<K: Send, V: Send> Send for RBTreeNode<K, V> {}

// SAFETY: If K and V can be accessed without synchronization, then it's also okay to access
// [`RBTreeNode`] without synchronization.
unsafe impl<K: Sync, V: Sync> Sync for RBTreeNode<K, V> {}

struct Node<K, V> {
    links: bindings::rb_node,
    key: K,
    value: V,
}
