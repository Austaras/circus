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
            let (inserted, _) = node.insert(data, None, Left, Black);

            inserted
        } else {
            self.node = Some(Box::new(Node::new(data)));

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
    fn new(data: T) -> Self {
        Self {
            data,
            color: Red,
            left: None,
            right: None,
        }
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

#[derive(PartialEq)]
enum Direction {
    Left,
    Right,
}

use Direction::*;

#[derive(Clone, Copy, Debug)]
enum Insert {
    One,
    Two(bool),
    Three,
    Four,
    Five,
    Six(bool),
}

use Insert::*;

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
            (Black, _, _) => One,
            // I2, parent is red, grand parent is black, repaint
            (Red, Some(Black), Red) => Two(false),
            // I3, root, do nothing
            // (None, _, _) => Three,
            // I4, child of red root, repaint
            (Red, None, _) => Four,
            // I5 or I6 based on child direction
            (Red, Some(Black), Black) => {
                if parent_dir != dir {
                    Five
                } else {
                    Six(false)
                }
            }
            _ => unreachable!(),
        };

        let l_color = self.left.as_ref().map(|l| l.color).unwrap_or(Black);
        let r_color = self.right.as_ref().map(|r| r.color).unwrap_or(Black);

        let (inserted, mut action, curr_action) = match self.data.cmp(&data) {
            Ordering::Equal => (false, None, Three),
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

        match action {
            Some(One) => action = None,
            Some(Two(false)) => action = Some(Two(true)),
            Some(Two(true)) => {
                self.color = Red;
                self.left.as_mut().unwrap().color = Black;
                self.right.as_mut().unwrap().color = Black;

                action = Some(curr_action);
            }
            Some(Three) => {
                action = None;
            }
            Some(Four) => {
                self.color = Black;
                action = None;
            }
            Some(Five) => {
                self.rotate(dir);
                action = Some(Six(true))
            }
            Some(Six(false)) => {
                action = Some(Six(true));
            }
            Some(Six(true)) => {
                self.rotate(dir);
                action = None
            }
            None => (),
        }

        (inserted, action)
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
        println!("{}", tree);
        tree.insert(9);
        println!("{}", tree);

        assert!(tree.search(&9));

        tree.check();

        let mut tree = RedBlackTree::new();

        tree.insert(5);
        tree.insert(7);
        tree.insert(6);

        assert!(tree.search(&6));

        tree.check();
    }
}
