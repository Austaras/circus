use std::{cmp::Ordering, fmt::Display, mem};

use arrayvec::ArrayVec;

pub struct BTree<T, const M: usize> {
    data: ArrayVec<T, M>,
    children: ArrayVec<Box<Node<T, M>>, M>,
}

struct Internal<T, const M: usize> {
    data: ArrayVec<T, M>,
    children: ArrayVec<Box<Node<T, M>>, M>,
}

enum Node<T, const M: usize> {
    Internal(Internal<T, M>),
    Leaf(ArrayVec<T, M>),
}

impl<T, const M: usize> BTree<T, M> {
    pub fn new() -> Self {
        BTree {
            data: ArrayVec::new(),
            children: ArrayVec::new(),
        }
    }
}

impl<T: Display, const M: usize> Display for BTree<T, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl<T: Eq + Ord, const M: usize> BTree<T, M> {
    fn search_child(child: &Node<T, M>, data: &T) -> Option<()> {
        match child {
            Node::Internal(intl) => match intl.data.binary_search(data) {
                Err(i) => Self::search_child(&intl.children[i], data),
                Ok(_) => Some(()),
            },
            Node::Leaf(l) => match l.binary_search(data) {
                Ok(_) => Some(()),
                Err(_) => None,
            },
        }
    }

    pub fn search(&self, data: &T) -> Option<()> {
        match self.data.binary_search(data) {
            Err(i) => {
                if self.children.len() > i {
                    Self::search_child(&self.children[i], data)
                } else {
                    None
                }
            }
            Ok(_) => Some(()),
        }
    }

    pub fn insert(&mut self, data: T) -> Option<T> {
        match self.data.binary_search(&data) {
            Ok(i) => Some(mem::replace(&mut self.data[i], data)),
            Err(i) => {
                if self.data.is_full() {
                    let mid = self.data.len() / 2;

                    match i.cmp(&mid) {
                        Ordering::Less => todo!(),
                        Ordering::Equal => todo!(),
                        Ordering::Greater => {
                            let mid = mid + 1;
                            let mut right = ArrayVec::new();

                            right.extend(self.data.drain(mid + 1..));

                            right.insert(i - mid - 1, data);

                            let right = Box::new(Node::Leaf(right));

                            let mid = self.data.pop().unwrap();

                            let left = mem::replace(&mut self.data, ArrayVec::new());

                            let left = Box::new(Node::Leaf(left));

                            self.data.push(mid);

                            self.children.push(left);
                            self.children.push(right);
                        }
                    }
                } else {
                    self.data.insert(i, data);
                }

                None
            }
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::BTree;

    impl<T: Eq + Ord, const M: usize> BTree<T, M> {
        fn check(&self) {
            for i in 0..self.data.len() - 1 {
                assert!(self.data[i] < self.data[i + 1])
            }
        }
    }

    #[test]
    fn basic() {
        let mut tree = BTree::<_, 5>::new();
        tree.insert(3);
        tree.insert(5);
        tree.insert(1);
        tree.insert(2);
        tree.insert(4);

        tree.check();

        assert_eq!(tree.search(&1), Some(()));
        assert_eq!(tree.search(&2), Some(()));
        assert_eq!(tree.search(&3), Some(()));
        assert_eq!(tree.search(&4), Some(()));
        assert_eq!(tree.search(&5), Some(()));
    }

    #[test]
    fn basic_split() {
        let mut tree = BTree::<_, 5>::new();
        tree.insert(3);
        tree.insert(6);
        tree.insert(4);
        tree.insert(1);
        tree.insert(2);
        tree.insert(5);

        tree.check();

        assert_eq!(tree.search(&5), Some(()));
    }
}
