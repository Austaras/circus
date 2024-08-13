use std::{
    cmp::Ordering,
    fmt::{Display, Write},
};

pub struct RedBlackTree<T> {
    node: Option<Box<Node<T>>>,
}

impl<T> RedBlackTree<T> {
    pub fn new() -> Self {
        Self { node: None }
    }
}

impl<T: Display> Display for RedBlackTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;

        if let Some(node) = &self.node {
            node.fmt(f)?;
        }

        f.write_char(')')?;

        Ok(())
    }
}

impl<T: Eq + Ord> RedBlackTree<T> {
    pub fn insert(&mut self, data: T) -> bool {
        if let Some(node) = &mut self.node {
            node.insert(data)
        } else {
            self.node = Some(Box::new(Node::new(data, Red)));

            true
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        None
    }

    pub fn search(&self, data: &T) -> bool {
        if let Some(node) = &self.node {
            node.search(data)
        } else {
            false
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Color {
    Red,
    Black,
}

impl Display for Color {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Red => f.write_char('R'),
            Black => f.write_char('B'),
        }
    }
}

use Color::*;

struct Node<T> {
    data: T,
    left: Option<Box<Self>>,
    right: Option<Box<Self>>,
    color: Color,
}

impl<T> Node<T> {
    fn new(data: T, color: Color) -> Self {
        Self {
            data,
            color,
            left: None,
            right: None,
        }
    }
}

impl<T: Display> Display for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)?;
        f.write_char('/')?;
        self.color.fmt(f)?;

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
                    self.left = Some(Box::new(Node::new(data, Red)));
                    true
                }
            }
            Ordering::Less => {
                if let Some(right) = &mut self.right {
                    right.insert(data)
                } else {
                    self.right = Some(Box::new(Node::new(data, Red)));
                    true
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
    use super::{Color::*, Node, RedBlackTree};

    impl<T: Eq + Ord> RedBlackTree<T> {
        fn check(&self) {
            if let Some(node) = &self.node {
                node.check();
            }
        }
    }

    impl<T: Eq + Ord> Node<T> {
        fn check(&self) -> usize {
            let lpath = if let Some(left) = &self.left {
                assert!(left.data < self.data);

                if self.color == Red {
                    assert_eq!(left.color, Black);
                }

                left.check()
            } else {
                0
            };

            let rpath = if let Some(right) = &self.right {
                assert!(right.data > self.data);

                if self.color == Red {
                    assert_eq!(right.color, Black);
                }

                right.check()
            } else {
                0
            };

            assert_eq!(lpath, rpath);

            lpath
                + match self.color {
                    Red => 0,
                    Black => 1,
                }
        }
    }

    #[test]
    fn baisc() {
        let mut tree = RedBlackTree::new();

        tree.insert(5);
        tree.insert(3);
        tree.insert(7);

        assert!(tree.search(&5));

        println!("{}", tree);

        // tree.check()
    }
}
