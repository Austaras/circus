use std::cmp::Ordering;

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

enum Search {
    Less,
    Greater,
    Exact(usize),
    Between(usize),
}

impl<T: Eq + Ord, const M: usize> BTree<T, M> {
    fn binary_search(arr: &ArrayVec<T, M>, data: &T) -> Search {
        if data < &arr[0] {
            return Search::Less;
        }

        if data > arr.last().unwrap() {
            return Search::Greater;
        }

        let mut curr = arr.len() / 2;

        while curr < arr.len() {
            match arr[curr].cmp(data) {
                Ordering::Less => {
                    if curr + 1 < arr.len() && &arr[curr + 1] > data {
                        return Search::Between(curr);
                    } else {
                        curr = (arr.len() + curr) / 2
                    }
                }
                Ordering::Equal => return Search::Exact(curr),
                Ordering::Greater => {
                    if curr >= 1 && &arr[curr - 1] < data {
                        return Search::Between(curr - 1);
                    } else {
                        curr = curr / 2
                    }
                }
            }
        }

        unreachable!()
    }

    fn search_child(child: &Node<T, M>, data: &T) -> bool {
        match child {
            Node::Internal(intl) => match Self::binary_search(&intl.data, data) {
                Search::Less => Self::search_child(&intl.children[0], data),
                Search::Greater => Self::search_child(intl.children.last().unwrap(), data),
                Search::Exact(_) => true,
                Search::Between(i) => Self::search_child(&intl.children[i + 1], data),
            },
            Node::Leaf(l) => {
                if let Search::Exact(_) = Self::binary_search(l, data) {
                    true
                } else {
                    false
                }
            }
        }
    }

    pub fn search(&self, data: &T) -> bool {
        match Self::binary_search(&self.data, data) {
            Search::Less => {
                if self.children.len() > 0 {
                    Self::search_child(&self.children[0], data)
                } else {
                    false
                }
            }
            Search::Greater => {
                if self.children.len() > self.data.len() + 1 {
                    Self::search_child(self.children.last().unwrap(), data)
                } else {
                    false
                }
            }
            Search::Exact(_) => true,
            Search::Between(i) => {
                if self.children.len() > i + 1 {
                    Self::search_child(&self.children[i + 1], data)
                } else {
                    false
                }
            }
        }
    }

    pub fn insert(&mut self, data: T) -> bool {
        false
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::BTree;
}
