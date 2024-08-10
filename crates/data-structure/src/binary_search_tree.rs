use std::{
    cmp::Ordering,
    fmt::{Display, Write},
    mem,
};

pub struct BinarySearchTree<T> {
    node: Option<Box<Node<T>>>,
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
            self.node = Some(Box::new(Node::new(data)));
            true
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        Node::delete(&mut self.node, data)
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

    fn delete(node: &mut Option<Box<Node<T>>>, data: &T) -> Option<T> {
        if let Some(n) = node {
            match n.data.cmp(data) {
                Ordering::Greater => Node::delete(&mut n.left, data),
                Ordering::Less => Node::delete(&mut n.right, data),
                Ordering::Equal => {
                    let curr = mem::replace(node, None).unwrap();

                    match (curr.left, curr.right) {
                        (None, None) => (),
                        (Some(child), None) | (None, Some(child)) => *node = Some(child),
                        (Some(mut l), Some(r)) => {
                            if l.right.is_some() {
                                let mut lr = &mut l.right;

                                while lr.as_ref().unwrap().right.is_some() {
                                    lr = &mut lr.as_mut().unwrap().right;
                                }

                                let lr = mem::replace(lr, None).unwrap();

                                l.right = lr.left;

                                let new_node = Node {
                                    data: lr.data,
                                    left: Some(l),
                                    right: Some(r),
                                };

                                *node = Some(Box::new(new_node));
                            } else {
                                l.right = Some(r);

                                *node = Some(l)
                            }
                        }
                    }

                    Some(curr.data)
                }
            }
        } else {
            None
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
    use super::{BinarySearchTree, Node};

    impl<T: Eq + Ord> BinarySearchTree<T> {
        fn check(&self) {
            if let Some(node) = &self.node {
                node.check()
            }
        }
    }

    impl<T: Eq + Ord> Node<T> {
        fn check(&self) {
            if let Some(left) = &self.left {
                assert!(left.data < self.data);

                left.check();
            }

            if let Some(right) = &self.right {
                assert!(right.data > self.data);

                right.check();
            }
        }
    }

    #[test]
    fn basic() {
        let mut tree = BinarySearchTree::new();
        tree.insert(1);
        tree.insert(3);
        tree.insert(5);
        tree.insert(7);

        tree.check();

        assert!(tree.search(&5));
        assert!(tree.search(&7));
    }

    #[test]
    fn delete_leaf() {
        let mut tree = BinarySearchTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        tree.check();

        tree.delete(&3);
        tree.check();

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
        tree.check();

        tree.delete(&5);
        tree.check();

        assert!(!tree.search(&5));
        assert!(tree.search(&6));
    }

    #[test]
    fn delete_root_simple() {
        let mut tree = BinarySearchTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        tree.check();

        tree.delete(&5);
        tree.check();

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
        tree.check();

        tree.delete(&11);
        tree.check();

        assert!(!tree.search(&11));
        assert!(tree.search(&9));
    }
}
