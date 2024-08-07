use std::{
    cmp::Ordering,
    fmt::{Display, Write},
    mem,
};

pub struct BinarySearchTree<T> {
    node: Option<Node<T>>,
}

impl<T> BinarySearchTree<T> {
    pub fn new() -> Self {
        Self { node: None }
    }
}

impl<T: Display> Display for BinarySearchTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;

        if let Some(node) = &self.node {
            node.fmt(f)?;
        }

        f.write_char(')')?;

        Ok(())
    }
}

impl<T: Eq + Ord> BinarySearchTree<T> {
    pub fn insert(&mut self, data: T) -> bool {
        if let Some(node) = &mut self.node {
            node.insert(data)
        } else {
            self.node = Some(Node::new(data));
            true
        }
    }

    pub fn delete(&mut self, data: &T) -> bool {
        if let Some(node) = &mut self.node {
            match node.delete(data) {
                Some(r) => r,
                None => {
                    self.node = None;
                    true
                }
            }
        } else {
            false
        }
    }

    pub fn search(&self, data: &T) -> bool {
        if let Some(node) = &self.node {
            node.search(data)
        } else {
            false
        }
    }
}

struct Node<T> {
    data: T,
    left: Option<Box<Self>>,
    right: Option<Box<Self>>,
}

impl<T> Node<T> {
    pub fn new(data: T) -> Self {
        Self {
            data,
            left: None,
            right: None,
        }
    }
}

impl<T: Display> Display for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)?;

        if let Some(left) = &self.left {
            f.write_char(' ')?;
            f.write_char('(')?;
            left.fmt(f)?;
            f.write_char(')')?;
        }

        if let Some(right) = &self.right {
            if self.left.is_none() {
                f.write_str(" ()")?;
            }

            f.write_char(' ')?;
            f.write_char('(')?;
            right.fmt(f)?;
            f.write_char(')')?;
        }

        Ok(())
    }
}

impl<T: Eq + Ord> Node<T> {
    fn insert(&mut self, data: T) -> bool {
        match self.data.cmp(&data) {
            Ordering::Equal => false,
            Ordering::Greater => {
                if let Some(left) = &mut self.left {
                    left.insert(data)
                } else {
                    self.left = Some(Box::new(Node::new(data)));
                    true
                }
            }
            Ordering::Less => {
                if let Some(right) = &mut self.right {
                    right.insert(data)
                } else {
                    self.right = Some(Box::new(Node::new(data)));
                    true
                }
            }
        }
    }

    fn delete(&mut self, data: &T) -> Option<bool> {
        match self.data.cmp(data) {
            Ordering::Equal => match (&mut self.left, &mut self.right) {
                (None, None) => None,
                (None, Some(r)) => {
                    mem::swap(&mut self.data, &mut r.data);
                    mem::swap(&mut self.left, &mut r.left);

                    let mut rr = None;
                    mem::swap(&mut rr, &mut r.right);
                    self.right = rr;

                    Some(true)
                }
                (Some(l), None) => {
                    mem::swap(&mut self.data, &mut l.data);
                    mem::swap(&mut self.right, &mut l.right);

                    let mut ll = None;
                    mem::swap(&mut ll, &mut l.left);
                    self.left = ll;

                    Some(true)
                }
                (Some(l), Some(_)) => {
                    let parent = &mut **l as *mut Node<T>;
                    if let Some(r) = &mut l.right {
                        let mut lr = &mut **r;
                        let mut parent = parent;

                        while lr.right.is_some() {
                            parent = lr as *mut Node<T>;
                            lr = lr.right.as_mut().unwrap();
                        }

                        mem::swap(&mut self.data, &mut lr.data);

                        unsafe {
                            mem::swap(&mut (*parent).right, &mut lr.left);
                        }

                        Some(true)
                    } else {
                        mem::swap(&mut self.data, &mut l.data);

                        let mut ll = None;
                        mem::swap(&mut ll, &mut l.left);
                        self.left = ll;

                        Some(true)
                    }
                }
            },
            Ordering::Greater => {
                if let Some(left) = &mut self.left {
                    match left.delete(data) {
                        None => {
                            self.left = None;
                            Some(true)
                        }
                        Some(r) => Some(r),
                    }
                } else {
                    Some(false)
                }
            }
            Ordering::Less => {
                if let Some(right) = &mut self.right {
                    match right.delete(data) {
                        None => {
                            self.right = None;
                            Some(true)
                        }
                        Some(r) => Some(r),
                    }
                } else {
                    Some(false)
                }
            }
        }
    }

    fn search(&self, data: &T) -> bool {
        match self.data.cmp(data) {
            Ordering::Equal => true,
            Ordering::Greater => {
                if let Some(left) = &self.left {
                    left.search(data)
                } else {
                    false
                }
            }
            Ordering::Less => {
                if let Some(right) = &self.right {
                    right.search(data)
                } else {
                    false
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::binary_search_tree::BinarySearchTree;

    #[test]
    fn basic() {
        let mut tree = BinarySearchTree::new();
        tree.insert(1);
        tree.insert(3);
        tree.insert(5);
        tree.insert(7);

        assert!(tree.search(&5));
        assert!(tree.search(&7));
    }

    #[test]
    fn delete_leaf() {
        let mut tree = BinarySearchTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);

        tree.delete(&3);

        assert!(!tree.search(&3));
        assert!(tree.search(&7));
    }

    #[test]
    fn delete_root_right_only() {
        let mut tree = BinarySearchTree::new();
        tree.insert(5);
        tree.insert(7);
        tree.insert(6);
        tree.insert(9);

        tree.delete(&5);

        assert!(!tree.search(&5));
        assert!(tree.search(&6));
    }

    #[test]
    fn delete_root_simple() {
        let mut tree = BinarySearchTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);

        tree.delete(&5);

        assert!(!tree.search(&5));
        assert!(tree.search(&7));
    }

    #[test]
    fn delete_root() {
        let mut tree = BinarySearchTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(11);
        tree.insert(8);
        tree.insert(12);
        tree.insert(7);
        tree.insert(10);
        tree.insert(9);
        tree.insert(12);

        tree.delete(&11);

        assert!(!tree.search(&11));
        assert!(tree.search(&9));
    }
}
