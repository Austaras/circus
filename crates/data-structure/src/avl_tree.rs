use std::{
    cmp::Ordering,
    fmt::{Display, Write},
    mem,
};

pub struct AVLTree<T> {
    node: Option<Box<Node<T>>>,
}

impl<T> AVLTree<T> {
    pub fn new() -> Self {
        Self { node: None }
    }
}

impl<T: Display> Display for AVLTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;

        if let Some(node) = &self.node {
            node.fmt(f)?;
        }

        f.write_char(')')?;

        Ok(())
    }
}

impl<T: Eq + Ord> AVLTree<T> {
    pub fn insert(&mut self, data: T) -> bool {
        if let Some(node) = &mut self.node {
            node.insert(data).is_some()
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
    balance: i8,
}

impl<T> Node<T> {
    pub fn new(data: T) -> Self {
        Self {
            data,
            left: None,
            right: None,
            balance: 0,
        }
    }
}

impl<T: Display> Display for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)?;
        f.write_char('/')?;
        self.balance.fmt(f)?;

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

#[derive(Clone, Copy, Debug)]
enum Direction {
    Left,
    Right,
}
use Direction::*;

impl<T: Eq + Ord> Node<T> {
    fn rotate_left_inner(&mut self) {
        mem::swap(&mut self.left, &mut self.right);
        let left = self.left.as_mut().unwrap();
        mem::swap(&mut self.data, &mut left.data);
        mem::swap(&mut left.left, &mut self.right);
        mem::swap(&mut left.right, &mut self.right);
    }

    fn rotate_left(&mut self) {
        self.rotate_left_inner();

        let left = self.left.as_mut().unwrap();

        if left.balance == 0 {
            left.balance = 1;
            self.balance = -1
        } else {
            left.balance = 0;
            self.balance = 0
        }
    }

    fn rotate_right_inner(&mut self) {
        mem::swap(&mut self.left, &mut self.right);
        let right = self.right.as_mut().unwrap();
        mem::swap(&mut self.data, &mut right.data);
        mem::swap(&mut right.right, &mut self.left);
        mem::swap(&mut right.left, &mut self.left);
    }

    fn rotate_right(&mut self) {
        self.rotate_right_inner();

        let right = self.right.as_mut().unwrap();

        if right.balance == 0 {
            right.balance = -1;
            self.balance = 1
        } else {
            right.balance = 0;
            self.balance = 0
        }
    }

    fn rotate_right_left(&mut self) {
        let right = self.right.as_mut().unwrap();
        let right_left_balance = right.left.as_ref().unwrap().balance;

        right.rotate_right_inner();
        self.rotate_left_inner();

        let left = self.left.as_mut().unwrap();
        let right = self.right.as_mut().unwrap();

        match right_left_balance {
            0 => {
                left.balance = 0;
                right.balance = 0;
            }
            1 => {
                left.balance = -1;
                right.balance = 0;
            }
            -1 => {
                left.balance = 0;
                right.balance = 1;
            }
            _ => unreachable!(),
        };

        self.balance = 0;
    }

    fn rotate_left_right(&mut self) {
        let left = self.left.as_mut().unwrap();
        let left_right_balance = left.right.as_ref().unwrap().balance;

        left.rotate_left_inner();
        self.rotate_right_inner();

        let left = self.left.as_mut().unwrap();
        let right = self.right.as_mut().unwrap();

        match left_right_balance {
            0 => {
                left.balance = 0;
                right.balance = 0;
            }
            1 => {
                left.balance = -1;
                right.balance = 0;
            }
            -1 => {
                left.balance = 0;
                right.balance = 1;
            }
            _ => unreachable!(),
        };

        self.balance = 0;
    }

    fn insert(&mut self, data: T) -> Option<(i8, bool)> {
        let mut dir = Left;

        let (child_balance, need_update) = match self.data.cmp(&data) {
            Ordering::Equal => return None,
            Ordering::Greater => {
                if let Some(left) = &mut self.left {
                    left.insert(data)
                } else {
                    self.left = Some(Box::new(Node::new(data)));
                    Some((-1, true))
                }
            }
            Ordering::Less => {
                if let Some(right) = &mut self.right {
                    dir = Right;
                    right.insert(data)
                } else {
                    self.right = Some(Box::new(Node::new(data)));
                    dir = Right;
                    Some((1, true))
                }
            }
        }?;

        if need_update {
            self.balance += match dir {
                Left => -1,
                Right => 1,
            } * child_balance.abs();

            if self.balance.abs() == 2 {
                match (child_balance, dir) {
                    // left left
                    (-1, Left) => self.rotate_right(),
                    // right left
                    (-1, Right) => self.rotate_right_left(),
                    // left right
                    (1, Left) => self.rotate_left_right(),
                    // right right
                    (1, Right) => self.rotate_left(),
                    (0, _) => (),
                    _ => unreachable!(),
                };

                Some((self.balance, false))
            } else {
                Some((self.balance, true))
            }
        } else {
            Some((self.balance, false))
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
                                    balance: curr.balance,
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
    use super::{AVLTree, Node};

    impl<T: Eq + Ord> AVLTree<T> {
        fn check(&self) {
            if let Some(node) = &self.node {
                node.check();
            }
        }
    }

    impl<T: Eq + Ord> Node<T> {
        fn check(&self) -> u8 {
            assert!(self.balance.abs() <= 1);

            let mut left_h = 0;
            let mut right_h = 0;

            if let Some(left) = &self.left {
                assert!(left.data < self.data);

                left_h = left.check();
            }

            if let Some(right) = &self.right {
                assert!(right.data > self.data);

                right_h = right.check();
            }

            assert_eq!(right_h as i8 - left_h as i8, self.balance);

            1 + left_h.max(right_h)
        }
    }

    #[test]
    fn basic_single() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        tree.insert(6);
        tree.insert(9);

        tree.check();

        tree.insert(10);

        tree.check();

        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(6);
        tree.insert(1);
        tree.insert(4);

        tree.check();

        tree.insert(0);

        tree.check();
    }

    #[test]
    fn basic_double() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(2);
        tree.insert(10);
        tree.insert(1);
        tree.insert(8);
        tree.insert(11);
        tree.insert(12);
        tree.insert(7);
        tree.insert(9);

        tree.check();

        tree.insert(6);

        tree.check();

        let mut tree = AVLTree::new();
        tree.insert(9);
        tree.insert(4);
        tree.insert(10);
        tree.insert(12);
        tree.insert(3);
        tree.insert(6);
        tree.insert(2);
        tree.insert(5);
        tree.insert(7);

        tree.check();

        tree.insert(8);

        tree.check();
    }

    #[test]
    fn simple_right_left() {
        let mut tree = AVLTree::new();
        tree.insert(4);
        tree.insert(6);
        tree.insert(5);

        tree.check();
    }

    #[test]
    fn single_propgate() {
        let mut tree = AVLTree::new();
        tree.insert(8);
        tree.insert(4);
        tree.insert(10);
        tree.insert(12);
        tree.insert(3);
        tree.insert(5);
        tree.insert(6);

        tree.check();

        tree.insert(7);

        tree.check();
    }
}
