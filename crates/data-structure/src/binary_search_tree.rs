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
    pub fn insert(&mut self, data: T) -> Option<T> {
        if let Some(node) = &mut self.node {
            node.insert(data)
        } else {
            self.node = Some(Box::new(Node::new(data)));
            None
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        Node::delete(&mut self.node, data)
    }

    pub fn search(&self, data: &T) -> Option<()> {
        if let Some(node) = &self.node {
            node.search(data)
        } else {
            None
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

    fn delete_rightmost(&mut self) -> Option<T> {
        if let Some(right) = self.right.as_mut() {
            if let Some(data) = right.delete_rightmost() {
                Some(data)
            } else {
                let right = mem::replace(&mut self.right, None).unwrap();
                self.right = right.left;

                Some(right.data)
            }
        } else {
            None
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
    fn insert(&mut self, data: T) -> Option<T> {
        match self.data.cmp(&data) {
            Ordering::Equal => Some(mem::replace(&mut self.data, data)),
            Ordering::Greater => {
                if let Some(left) = &mut self.left {
                    left.insert(data)
                } else {
                    self.left = Some(Box::new(Node::new(data)));
                    None
                }
            }
            Ordering::Less => {
                if let Some(right) = &mut self.right {
                    right.insert(data)
                } else {
                    self.right = Some(Box::new(Node::new(data)));
                    None
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
                            let data = l.delete_rightmost();

                            if let Some(data) = data {
                                let new_node = Node {
                                    data: data,
                                    left: Some(l),
                                    right: Some(r),
                                };

                                *node = Some(Box::new(new_node))
                            } else {
                                let new_node = Node {
                                    data: l.data,
                                    left: l.left,
                                    right: Some(r),
                                };

                                *node = Some(Box::new(new_node))
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

    fn search(&self, data: &T) -> Option<()> {
        match self.data.cmp(data) {
            Ordering::Equal => Some(()),
            Ordering::Greater => {
                if let Some(left) = &self.left {
                    left.search(data)
                } else {
                    None
                }
            }
            Ordering::Less => {
                if let Some(right) = &self.right {
                    right.search(data)
                } else {
                    None
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

        assert_eq!(tree.search(&5), Some(()));
        assert_eq!(tree.search(&7), Some(()));
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

        assert_eq!(tree.search(&3), None);
        assert_eq!(tree.search(&7), Some(()));
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

        assert_eq!(tree.search(&5), None);
        assert_eq!(tree.search(&6), Some(()));
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

        assert_eq!(tree.search(&5), None);
        assert_eq!(tree.search(&7), Some(()));
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

        assert_eq!(tree.search(&11), None);
        assert_eq!(tree.search(&9), Some(()));
    }

    #[test]
    fn delete_chain() {
        let mut tree = BinarySearchTree::new();
        tree.insert(11);
        tree.insert(12);
        tree.insert(3);
        tree.insert(5);
        tree.insert(7);
        tree.insert(9);
        tree.insert(8);
        tree.check();

        tree.delete(&11);
        tree.check();

        assert_eq!(tree.search(&8), Some(()));
        assert_eq!(tree.search(&7), Some(()));
    }
}
