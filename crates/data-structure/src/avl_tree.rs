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
    pub fn insert(&mut self, data: T) -> Option<T> {
        if let Some(node) = &mut self.node {
            node.insert(data).1
        } else {
            self.node = Some(Box::new(Node::new(data)));
            None
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        Node::delete(&mut self.node, data).map(|(data, _)| data)
    }

    pub fn search(&self, data: &T) -> Option<()> {
        if let Some(node) = &self.node {
            node.search(data)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Balance {
    LHeavy,
    RHeavy,
    Balanced,
}

impl Display for Balance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LHeavy => f.write_char('L'),
            RHeavy => f.write_char('R'),
            Balanced => f.write_char('B'),
        }
    }
}
use Balance::*;

struct Node<T> {
    data: T,
    left: Option<Box<Self>>,
    right: Option<Box<Self>>,
    balance: Balance,
}

impl<T> Node<T> {
    fn new(data: T) -> Self {
        Self {
            data,
            left: None,
            right: None,
            balance: Balanced,
        }
    }

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

        if left.balance == Balanced {
            left.balance = RHeavy;
            self.balance = LHeavy
        } else {
            left.balance = Balanced;
            self.balance = Balanced
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

        if right.balance == Balanced {
            right.balance = LHeavy;
            self.balance = RHeavy
        } else {
            right.balance = Balanced;
            self.balance = Balanced
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
            Balanced => {
                left.balance = Balanced;
                right.balance = Balanced;
            }
            RHeavy => {
                left.balance = LHeavy;
                right.balance = Balanced;
            }
            LHeavy => {
                left.balance = Balanced;
                right.balance = RHeavy;
            }
        };

        self.balance = Balanced;
    }

    fn rotate_left_right(&mut self) {
        let left = self.left.as_mut().unwrap();
        let left_right_balance = left.right.as_ref().unwrap().balance;

        left.rotate_left_inner();
        self.rotate_right_inner();

        let left = self.left.as_mut().unwrap();
        let right = self.right.as_mut().unwrap();

        match left_right_balance {
            Balanced => {
                left.balance = Balanced;
                right.balance = Balanced;
            }
            RHeavy => {
                left.balance = LHeavy;
                right.balance = Balanced;
            }
            LHeavy => {
                left.balance = Balanced;
                right.balance = RHeavy;
            }
        };

        self.balance = Balanced;
    }

    fn delete_rightmost(node: &mut Option<Box<Node<T>>>) -> (T, bool) {
        let node_inner = node.as_mut().unwrap();

        if node_inner.right.is_some() {
            let (data, mut should_update) = Node::delete_rightmost(&mut node_inner.right);

            if should_update {
                match node_inner.balance {
                    RHeavy => node_inner.balance = Balanced,
                    Balanced => {
                        node_inner.balance = LHeavy;
                        should_update = false;
                    }
                    LHeavy => {
                        if node_inner.right.as_ref().map(|r| r.balance) == Some(LHeavy) {
                            node_inner.rotate_left_right()
                        } else {
                            node_inner.rotate_right()
                        }
                    }
                }
            }

            (data, should_update)
        } else {
            let node = mem::replace(node, None).unwrap();

            (node.data, true)
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
    fn insert(&mut self, data: T) -> (Option<(Balance, bool)>, Option<T>) {
        let mut dir = Left;

        let (child, ret_data) = match self.data.cmp(&data) {
            Ordering::Equal => return (None, Some(mem::replace(&mut self.data, data))),
            Ordering::Greater => {
                if let Some(left) = &mut self.left {
                    left.insert(data)
                } else {
                    self.left = Some(Box::new(Node::new(data)));
                    (Some((LHeavy, true)), None)
                }
            }
            Ordering::Less => {
                if let Some(right) = &mut self.right {
                    dir = Right;
                    right.insert(data)
                } else {
                    self.right = Some(Box::new(Node::new(data)));
                    dir = Right;
                    (Some((RHeavy, true)), None)
                }
            }
        };

        let Some((child_balance, need_update)) = child else {
            return (None, ret_data);
        };

        let balance = if need_update {
            match (dir, self.balance) {
                (Left, RHeavy) => {
                    self.balance = Balanced;

                    Some((self.balance, false))
                }
                (Left, LHeavy) => {
                    if child_balance == RHeavy {
                        self.rotate_left_right()
                    } else {
                        self.rotate_right()
                    }

                    Some((self.balance, false))
                }
                (Left, Balanced) => {
                    self.balance = LHeavy;
                    Some((self.balance, true))
                }
                (Right, RHeavy) => {
                    if child_balance == LHeavy {
                        self.rotate_right_left()
                    } else {
                        self.rotate_left()
                    }

                    Some((self.balance, false))
                }
                (Right, LHeavy) => {
                    self.balance = Balanced;

                    Some((self.balance, false))
                }
                (Right, Balanced) => {
                    self.balance = RHeavy;
                    Some((self.balance, true))
                }
            }
        } else {
            Some((self.balance, false))
        };

        (balance, ret_data)
    }

    fn delete(node: &mut Option<Box<Node<T>>>, data: &T) -> Option<(T, bool)> {
        let mut dir = Left;

        let (data, mut should_update) = if let Some(n) = node {
            match n.data.cmp(data) {
                Ordering::Greater => Node::delete(&mut n.left, data),
                Ordering::Less => {
                    dir = Right;
                    Node::delete(&mut n.right, data)
                }
                Ordering::Equal => {
                    let curr = mem::replace(node, None).unwrap();

                    let mut should_update = true;

                    match (curr.left, curr.right) {
                        (None, None) => (),
                        (Some(mut child), None) => {
                            child.balance = curr.balance;
                            *node = Some(child);
                        }
                        (None, Some(mut child)) => {
                            dir = Right;
                            child.balance = curr.balance;
                            *node = Some(child);
                        }
                        (Some(mut l), Some(r)) => {
                            if l.right.is_some() {
                                let (new_data, should_update_inner) =
                                    Node::delete_rightmost(&mut l.right);

                                if !should_update_inner {
                                    should_update = false
                                } else {
                                    match l.balance {
                                        RHeavy => l.balance = Balanced,
                                        Balanced => {
                                            l.balance = LHeavy;
                                            should_update = false;
                                        }
                                        LHeavy => {
                                            if l.right.as_ref().map(|r| r.balance) == Some(LHeavy) {
                                                l.rotate_left_right()
                                            } else {
                                                l.rotate_right()
                                            }
                                        }
                                    }
                                }

                                let new_node = Node {
                                    data: new_data,
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
                    };

                    Some((curr.data, should_update))
                }
            }
        } else {
            None
        }?;

        if should_update {
            if let Some(node) = node.as_mut() {
                match (dir, node.balance) {
                    (Left, LHeavy) | (Right, RHeavy) => node.balance = Balanced,
                    (Left, Balanced) => {
                        node.balance = RHeavy;
                        should_update = false;
                    }
                    (Right, Balanced) => {
                        node.balance = LHeavy;
                        should_update = false;
                    }
                    (Left, RHeavy) => {
                        let right = node.right.as_ref().unwrap();

                        if right.balance == LHeavy {
                            node.rotate_right_left()
                        } else {
                            node.rotate_left()
                        }
                    }
                    (Right, LHeavy) => {
                        let left = node.left.as_ref().unwrap();

                        if left.balance == RHeavy {
                            node.rotate_left_right();
                        } else {
                            node.rotate_right()
                        }
                    }
                }
            }
        }

        Some((data, should_update))
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
    use super::{
        AVLTree,
        Balance::{self, *},
        Node,
    };

    impl<T: Eq + Ord> AVLTree<T> {
        fn check(&self) {
            if let Some(node) = &self.node {
                node.check();
            }
        }
    }

    impl Balance {
        fn to_isize(self) -> isize {
            match self {
                LHeavy => -1,
                RHeavy => 1,
                Balanced => 0,
            }
        }
    }

    impl<T: Eq + Ord> Node<T> {
        fn check(&self) -> usize {
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

            assert_eq!(
                right_h.wrapping_sub(left_h) as isize,
                self.balance.to_isize()
            );

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

    #[test]
    fn simple_delete() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(4);
        tree.insert(6);

        tree.check();

        tree.delete(&5);

        tree.check();

        let mut tree = AVLTree::new();
        tree.insert(9);
        tree.insert(7);
        tree.insert(10);
        tree.insert(6);
        tree.insert(8);
        tree.check();

        tree.delete(&9);

        tree.check();
    }

    #[test]
    fn simple_delete_rotate() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(6);
        tree.insert(1);
        tree.insert(2);

        tree.check();

        tree.delete(&6);

        tree.check();

        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(8);
        tree.insert(6);
        tree.insert(9);

        tree.check();

        tree.delete(&3);

        tree.check();
    }

    #[test]
    fn simple_delete_rightmost() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        tree.insert(1);
        tree.check();

        tree.delete(&5);

        tree.check();
    }

    #[test]
    fn delete_rotate_current() {
        let mut tree = AVLTree::new();
        tree.insert(6);
        tree.insert(4);
        tree.insert(8);
        tree.insert(9);
        tree.insert(2);
        tree.insert(5);
        tree.insert(6);

        tree.check();

        tree.delete(&4);

        tree.check();
    }

    #[test]
    fn delete_double_rotate() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(8);
        tree.insert(6);

        tree.check();

        tree.delete(&3);

        tree.check();

        let mut tree = AVLTree::new();
        tree.insert(8);
        tree.insert(5);
        tree.insert(10);
        tree.insert(3);
        tree.insert(6);
        tree.insert(12);
        tree.insert(4);

        tree.check();

        tree.delete(&3);

        tree.check();
    }

    #[test]
    fn delete_rotate_rightmost() {
        let mut tree = AVLTree::new();
        tree.insert(9);
        tree.insert(7);
        tree.insert(10);
        tree.insert(11);
        tree.insert(6);
        tree.insert(8);
        tree.insert(5);
        tree.check();

        tree.delete(&9);

        tree.check();
    }
}
