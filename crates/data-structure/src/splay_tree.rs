use std::{
    cmp::Ordering,
    fmt::{Display, Write},
    mem,
};

pub struct SplayTree<T> {
    node: Option<Box<Node<T>>>,
}

impl<T> SplayTree<T> {
    pub fn new() -> Self {
        Self { node: None }
    }
}

impl<T: Display> Display for SplayTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;

        if let Some(node) = &self.node {
            node.fmt(f)?;
        }

        f.write_char(')')?;

        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum Direction {
    Left,
    Right,
}

use Direction::*;

struct DelAction {
    start_rotate: bool,
    grand_child: Option<Direction>,
    child: Option<Direction>,
}

impl<T: Eq + Ord> SplayTree<T> {
    pub fn insert(&mut self, data: T) -> Option<T> {
        if let Some(node) = &mut self.node {
            let (ret, (dir1, dir2)) = node.insert(data);

            match (dir1, dir2) {
                (None, None) => (),
                (None, Some(Left)) => node.rotate_right(),
                (None, Some(Right)) => node.rotate_left(),
                (Some(_), None) => unreachable!(),
                (Some(dir1), Some(dir2)) => node.rotate(dir1, dir2),
            }

            ret
        } else {
            self.node = Some(Box::new(Node::new(data)));

            None
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        let (ret, dir) = Node::delete(&mut self.node, data);

        if let Some(node) = &mut self.node {
            if dir.start_rotate {
                match (dir.grand_child, dir.child) {
                    (None, None) => (),
                    (None, Some(Left)) => node.rotate_right(),
                    (None, Some(Right)) => node.rotate_left(),
                    (Some(_), None) => unreachable!(),
                    (Some(dir1), Some(dir2)) => node.rotate(dir1, dir2),
                }
            }
        }

        ret
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
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
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

impl<T> Node<T> {
    fn new(data: T) -> Self {
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

impl<T: Eq + Ord> Node<T> {
    fn rotate_left(&mut self) {
        mem::swap(&mut self.left, &mut self.right);
        let left = self.left.as_mut().unwrap();
        mem::swap(&mut self.data, &mut left.data);
        mem::swap(&mut left.left, &mut self.right);
        mem::swap(&mut left.right, &mut self.right);
    }

    fn rotate_right(&mut self) {
        mem::swap(&mut self.left, &mut self.right);
        let right = self.right.as_mut().unwrap();
        mem::swap(&mut self.data, &mut right.data);
        mem::swap(&mut right.right, &mut self.left);
        mem::swap(&mut right.left, &mut self.left);
    }

    fn rotate(&mut self, dir1: Direction, dir2: Direction) {
        match (dir1, dir2) {
            (Left, Left) => {
                self.rotate_right();
                self.rotate_right();
            }
            (Left, Right) => {
                self.right.as_mut().unwrap().rotate_right();
                self.rotate_left();
            }
            (Right, Left) => {
                self.left.as_mut().unwrap().rotate_left();
                self.rotate_right();
            }
            (Right, Right) => {
                self.rotate_left();
                self.rotate_left();
            }
        }
    }

    fn insert(&mut self, data: T) -> (Option<T>, (Option<Direction>, Option<Direction>)) {
        match data.cmp(&self.data) {
            Ordering::Less => {
                if let Some(left) = &mut self.left {
                    let (ret, (_, dir2)) = left.insert(data);

                    let dir = if let Some(dir2) = dir2 {
                        self.rotate(dir2, Left);
                        (None, None)
                    } else {
                        (dir2, Some(Left))
                    };

                    (ret, dir)
                } else {
                    self.left = Some(Box::new(Node::new(data)));

                    (None, (None, Some(Left)))
                }
            }
            Ordering::Equal => {
                let data = mem::replace(&mut self.data, data);

                (Some(data), (None, None))
            }
            Ordering::Greater => {
                if let Some(right) = &mut self.right {
                    let (ret, (_, dir2)) = right.insert(data);

                    let dir = if let Some(dir2) = dir2 {
                        self.rotate(dir2, Right);
                        (None, None)
                    } else {
                        (dir2, Some(Right))
                    };

                    (ret, dir)
                } else {
                    self.right = Some(Box::new(Node::new(data)));

                    (None, (None, Some(Right)))
                }
            }
        }
    }

    fn delete(node: &mut Option<Box<Node<T>>>, data: &T) -> (Option<T>, DelAction) {
        if let Some(n) = node {
            match n.data.cmp(data) {
                Ordering::Greater => {
                    let (ret, dir) = Node::delete(&mut n.left, data);

                    let dir = if ret.is_some() {
                        if !dir.start_rotate {
                            DelAction {
                                start_rotate: true,
                                ..dir
                            }
                        } else {
                            let (grand_child, child) = if let Some(child) = dir.child {
                                n.rotate(child, Left);
                                (None, None)
                            } else {
                                (dir.child, Some(Left))
                            };

                            DelAction {
                                start_rotate: true,
                                grand_child,
                                child,
                            }
                        }
                    } else {
                        dir
                    };

                    (ret, dir)
                }
                Ordering::Less => {
                    let (ret, dir) = Node::delete(&mut n.right, data);

                    let dir = if ret.is_some() {
                        if !dir.start_rotate {
                            DelAction {
                                start_rotate: true,
                                ..dir
                            }
                        } else {
                            let (grand_child, child) = if let Some(child) = dir.child {
                                n.rotate(child, Right);
                                (None, None)
                            } else {
                                (dir.child, Some(Right))
                            };

                            DelAction {
                                start_rotate: true,
                                grand_child,
                                child,
                            }
                        }
                    } else {
                        dir
                    };

                    (ret, dir)
                }
                Ordering::Equal => {
                    let curr = mem::replace(node, None).unwrap();

                    match (curr.left, curr.right) {
                        (None, None) => (),
                        (Some(child), None) | (None, Some(child)) => *node = Some(child),
                        (Some(mut l), Some(r)) => {
                            let data = l.delete_rightmost();

                            if let Some(data) = data {
                                let new_node = Node {
                                    data,
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

                    (
                        Some(curr.data),
                        DelAction {
                            start_rotate: false,
                            grand_child: None,
                            child: None,
                        },
                    )
                }
            }
        } else {
            (
                None,
                DelAction {
                    start_rotate: false,
                    grand_child: None,
                    child: None,
                },
            )
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
    use super::{Node, SplayTree};

    impl<T: Eq + Ord> SplayTree<T> {
        fn check(&self, root: &T) {
            if let Some(node) = &self.node {
                assert!(&node.data == root);
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
    fn basic_insert() {
        let mut tree = SplayTree::new();
        tree.insert(5);
        tree.insert(6);
        tree.insert(7);
        tree.insert(8);
        tree.insert(9);

        tree.check(&9);

        tree.insert(4);
        tree.insert(3);
        tree.insert(2);
        tree.insert(1);
        tree.insert(0);

        tree.check(&0);
    }

    #[test]
    fn basic_insert_2() {
        let mut tree = SplayTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(11);
        tree.insert(8);
        tree.insert(12);
        tree.insert(7);
        tree.insert(10);
        tree.insert(9);
        tree.insert(12);

        tree.check(&12);
    }

    #[test]
    fn basic_delete() {
        let mut tree = SplayTree::new();
        tree.insert(5);
        tree.insert(6);
        tree.insert(7);
        tree.insert(8);
        tree.insert(9);
        tree.insert(4);
        tree.insert(3);
        tree.insert(2);
        tree.insert(1);
        tree.insert(0);

        tree.check(&0);

        tree.delete(&4);

        tree.check(&3);

        tree.delete(&7);

        tree.check(&9);
    }
}
