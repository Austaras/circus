use std::{
    cmp::Ordering,
    fmt::{Display, Write},
    mem,
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
            let dir = match node.data.cmp(&data) {
                Ordering::Less => Right,
                Ordering::Equal | Ordering::Greater => Left,
            };

            let (inserted, _) = node.insert(data, None, dir, Black);

            inserted
        } else {
            self.node = Some(Box::new(Node::new(data)));

            true
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        Node::delete(&mut self.node, data, None, Black, Black, Black).1
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
    fn new(data: T) -> Self {
        Self {
            data,
            color: Red,
            left: None,
            right: None,
        }
    }

    fn left_color(&self) -> Color {
        self.left.as_ref().map(|l| l.color).unwrap_or(Black)
    }

    fn right_color(&self) -> Color {
        self.right.as_ref().map(|r| r.color).unwrap_or(Black)
    }

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

    fn rotate(&mut self, dir: Direction) {
        match dir {
            Left => self.rotate_right(),
            Right => self.rotate_left(),
        }
    }

    fn insert_action(
        &mut self,
        action: Option<Insert>,
        curr_action: Insert,
        dir: Direction,
    ) -> Option<Insert> {
        match action {
            Some(I1) => None,
            Some(I2Curr) => Some(I2Parent),
            Some(I2Parent) => {
                self.color = Red;
                self.left.as_mut().unwrap().color = Black;
                self.right.as_mut().unwrap().color = Black;

                Some(I2Grand)
            }
            Some(I2Grand) => self.insert_action(Some(curr_action), curr_action, dir),
            Some(I3) => None,
            Some(I4) => {
                self.color = Black;
                None
            }
            Some(I5) => {
                self.rotate(dir);
                Some(I6Parent)
            }
            Some(I6Curr) => Some(I6Parent),
            Some(I6Parent) => {
                self.rotate(dir);
                None
            }
            None => None,
        }
    }

    fn delete_action_4(&mut self, dir: Direction) -> bool {
        self.color = Black;

        match dir {
            Left => self.right.as_mut().unwrap().color = Red,
            Right => self.left.as_mut().unwrap().color = Red,
        }

        false
    }

    fn delete_action_5(&mut self, dir: Direction) -> bool {
        match dir {
            Left => {
                let r = self.right.as_mut().unwrap();
                r.rotate_right();

                r.right.as_mut().unwrap().color = Red;

                if let Some(r) = r.right.as_mut().unwrap().right.as_mut() {
                    r.color = Black;
                }

                self.delete_action_6(dir)
            }
            Right => {
                let l = self.left.as_mut().unwrap();
                l.rotate_left();

                l.left.as_mut().unwrap().color = Red;

                if let Some(l) = l.left.as_mut().unwrap().left.as_mut() {
                    l.color = Black;
                }

                self.delete_action_6(dir)
            }
        }
    }

    fn delete_action_6(&mut self, dir: Direction) -> bool {
        match dir {
            Left => {
                self.rotate_left();
                self.right.as_mut().unwrap().color = Black
            }
            Right => {
                self.rotate_right();
                self.left.as_mut().unwrap().color = Black;
            }
        }

        false
    }

    fn delete_action(&mut self, action: Option<Delete>, dir: Direction) -> bool {
        match action {
            None | Some(D1) => false,
            Some(D2) => {
                match dir {
                    Left => self.right.as_mut().unwrap().color = Red,
                    Right => self.left.as_mut().unwrap().color = Red,
                };
                true
            }
            Some(D3) => match dir {
                Left => {
                    self.rotate_left();
                    self.left.as_mut().unwrap().color = Red;

                    let r = self.right.as_mut().unwrap();

                    match (r.left_color(), r.right_color()) {
                        (_, Red) => self.delete_action_6(dir),
                        (Red, Black) => self.delete_action_5(dir),
                        (Black, Black) => self.delete_action_4(dir),
                    }
                }
                Right => {
                    self.rotate_right();
                    self.right.as_mut().unwrap().color = Red;

                    let l = self.left.as_mut().unwrap();

                    match (l.right_color(), l.left_color()) {
                        (_, Red) => self.delete_action_6(dir),
                        (Red, Black) => self.delete_action_5(dir),
                        (Black, Black) => self.delete_action_4(dir),
                    }
                }
            },
            Some(D4) => self.delete_action_4(dir),
            Some(D5) => self.delete_action_5(dir),
            Some(D6) => self.delete_action_6(dir),
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

#[derive(PartialEq, Clone, Copy)]
enum Direction {
    Left,
    Right,
}

use Direction::*;

#[derive(Clone, Copy, Debug)]
enum Insert {
    I1,
    I2Grand,
    I2Parent,
    I2Curr,
    I3,
    I4,
    I5,
    I6Curr,
    I6Parent,
}

use Insert::*;

#[derive(Clone, Copy, Debug)]
enum Delete {
    D1,
    D2,
    D3,
    D4,
    D5,
    D6,
}

use Delete::*;

impl<T: Eq + Ord> Node<T> {
    fn insert(
        &mut self,
        data: T,
        parent: Option<Color>,
        parent_dir: Direction,
        uncle: Color,
    ) -> (bool, Option<Insert>) {
        let mut dir = Left;

        let curr_action = |dir| match (self.color, parent, uncle) {
            // I1, parent is black, do nothing
            (Black, _, _) => I1,
            // I2, parent is red, grand parent is black, repaint
            (Red, Some(Black), Red) => I2Curr,
            // I3, root, do nothing
            // (None, _, _) => Three,
            // I4, child of red root, repaint
            (Red, None, _) => I4,
            // I5 or I6 based on child direction
            (Red, Some(Black), Black) => {
                if parent_dir != dir {
                    I5
                } else {
                    I6Curr
                }
            }
            _ => unreachable!(),
        };

        let l_color = self.left.as_ref().map(|l| l.color).unwrap_or(Black);
        let r_color = self.right.as_ref().map(|r| r.color).unwrap_or(Black);

        let (inserted, action, curr_action) = match self.data.cmp(&data) {
            Ordering::Equal => (false, None, I3),
            Ordering::Greater => {
                let curr_action = curr_action(Left);
                if let Some(left) = &mut self.left {
                    let (inserted, action) = left.insert(data, Some(self.color), Left, r_color);

                    (inserted, action, curr_action)
                } else {
                    self.left = Some(Box::new(Node::new(data)));
                    (true, Some(curr_action), curr_action)
                }
            }
            Ordering::Less => {
                dir = Right;
                let curr_action = curr_action(Right);

                if let Some(right) = &mut self.right {
                    let (inserted, action) = right.insert(data, Some(self.color), Right, l_color);

                    (inserted, action, curr_action)
                } else {
                    self.right = Some(Box::new(Node::new(data)));
                    (true, Some(curr_action), curr_action)
                }
            }
        };

        let action = self.insert_action(action, curr_action, dir);

        (inserted, action)
    }

    fn delete(
        node: &mut Option<Box<Node<T>>>,
        data: &T,
        parent: Option<Color>,
        sibling: Color,
        close: Color,
        distant: Color,
    ) -> (Option<Delete>, Option<T>) {
        if let Some(n) = node {
            let mut action = match n.color {
                Red => None,
                Black => match (parent, sibling, close, distant) {
                    (None, _, _, _) => Some(D1),
                    (Some(Black), Black, Black, Black) => Some(D2),
                    (Some(Black), Red, Black, Black) => Some(D3),
                    (Some(Red), Black, Black, Black) => Some(D4),
                    (Some(_), Black, Red, Black) => Some(D5),
                    (Some(_), Black, _, Red) => Some(D6),
                    _ => todo!(),
                },
            };

            let new_parent = Some(n.color);

            match n.data.cmp(data) {
                Ordering::Greater => {
                    let (new_sibling, new_close, new_distant) = if let Some(r) = n.right.as_ref() {
                        (r.color, r.left_color(), r.right_color())
                    } else {
                        (Black, Black, Black)
                    };
                    let (curr_action, data) = Node::delete(
                        &mut n.left,
                        data,
                        new_parent,
                        new_sibling,
                        new_close,
                        new_distant,
                    );

                    let should_continue = n.delete_action(curr_action, Left);

                    if !should_continue {
                        action = None
                    }

                    (action, data)
                }
                Ordering::Less => {
                    let (new_sibling, new_close, new_distant) = if let Some(l) = n.left.as_ref() {
                        (l.color, l.right_color(), l.left_color())
                    } else {
                        (Black, Black, Black)
                    };
                    let (curr_action, data) = Node::delete(
                        &mut n.right,
                        data,
                        new_parent,
                        new_sibling,
                        new_close,
                        new_distant,
                    );

                    let should_continue = n.delete_action(curr_action, Right);

                    if !should_continue {
                        action = None
                    }

                    (action, data)
                }
                Ordering::Equal => {
                    let curr = mem::replace(node, None).unwrap();
                    let color = curr.color;
                    let mut curr_action = None;

                    match (curr.left, curr.right) {
                        (None, None) => curr_action = action,
                        (Some(mut child), None) | (None, Some(mut child)) => {
                            child.color = Black;
                            *node = Some(child)
                        }
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
                                    color,
                                    left: Some(l),
                                    right: Some(r),
                                };

                                *node = Some(Box::new(new_node));
                            } else {
                                l.right = Some(r);
                                l.color = color;

                                *node = Some(l)
                            }
                        }
                    }

                    (curr_action, Some(curr.data))
                }
            }
        } else {
            (None, None)
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
    fn basic() {
        let mut tree = RedBlackTree::new();

        tree.insert(5);
        tree.insert(7);
        tree.insert(3);

        assert!(tree.search(&5));

        tree.check();

        tree.insert(6);

        tree.check();
    }

    #[test]
    fn basic_rotate() {
        let mut tree = RedBlackTree::new();

        tree.insert(5);
        tree.insert(7);
        tree.insert(9);

        assert!(tree.search(&9));

        tree.check();

        let mut tree = RedBlackTree::new();

        tree.insert(5);
        tree.insert(7);
        tree.insert(6);

        assert!(tree.search(&6));

        tree.check();
    }

    #[test]
    fn basic_insert_bubble() {
        let mut tree = RedBlackTree::new();

        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(6);
        tree.insert(7);

        tree.check();
    }

    #[test]
    fn basic_delete() {
        let mut tree = RedBlackTree::new();

        tree.insert(14);
        tree.insert(7);
        tree.insert(3);

        tree.check();

        tree.delete(&7);

        tree.check();
    }

    #[test]
    fn basic_delete_action() {
        let mut tree = RedBlackTree::new();

        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(6);
        tree.insert(7);
        tree.insert(8);
        tree.insert(9);
        tree.insert(10);

        tree.delete(&10);
        tree.check();
        tree.delete(&9);
        tree.check();
        tree.delete(&8);
        tree.check();
        tree.delete(&7);
        tree.check();
    }

    #[test]
    fn basic_delete_rotate() {
        let mut tree = RedBlackTree::new();

        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(6);
        tree.insert(7);
        tree.insert(8);
        tree.insert(9);
        tree.insert(10);

        tree.delete(&10);
        tree.delete(&9);
        tree.delete(&8);
        tree.insert(9);
        tree.check();

        tree.delete(&5);
        tree.check();
    }

    #[test]
    fn delete_mutlti_rotate() {
        let mut tree = RedBlackTree::new();

        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(6);
        tree.insert(8);
        tree.insert(9);
        tree.insert(10);
        tree.insert(11);

        tree.delete(&11);
        tree.delete(&10);
        tree.delete(&8);
        tree.insert(7);
        tree.check();

        tree.delete(&5);
        tree.check();
    }
}
