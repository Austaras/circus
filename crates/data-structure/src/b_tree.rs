use std::{cmp::Ordering, fmt::Display, mem};

use arrayvec::ArrayVec;

pub struct BTree<T, const M: usize>
where
    [(); M + 1]:,
{
    data: ArrayVec<T, M>,
    children: ArrayVec<Box<Node<T, M>>, { M + 1 }>,
}
enum Node<T, const M: usize>
where
    [(); M + 1]:,
{
    Internal(BTree<T, M>),
    Leaf(ArrayVec<T, M>),
}

impl<T, const M: usize> BTree<T, M>
where
    [(); M + 1]:,
{
    pub fn new() -> Self {
        BTree {
            data: ArrayVec::new(),
            children: ArrayVec::new(),
        }
    }
}

impl<T: Display, const M: usize> Display for BTree<T, M>
where
    [(); M + 1]:,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

fn split<T, const M: usize>(
    mut arr: ArrayVec<T, M>,
    to_insert: usize,
    data: T,
) -> (ArrayVec<T, M>, T, ArrayVec<T, M>) {
    let mid = arr.len() / 2;
    match to_insert.cmp(&mid) {
        Ordering::Less => {
            let mid = mid - 1;
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid + 1..));

            let mid = arr.pop().unwrap();

            let mut left = arr;
            left.insert(to_insert, data);

            (left, mid, right)
        }
        Ordering::Equal => {
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid..));

            let left = arr;

            (left, data, right)
        }
        Ordering::Greater => {
            let mid = mid + 1;
            let mut right = ArrayVec::new();

            if mid + 1 < arr.len() {
                right.extend(arr.drain(mid + 1..));
                right.insert(to_insert - mid - 1, data);
            } else {
                right.push(data)
            }

            let mid = arr.pop().unwrap();

            let left = arr;

            (left, mid, right)
        }
    }
}

fn split_children<T, const M: usize>(
    mut arr: ArrayVec<T, M>,
    to_insert: usize,
    data: T,
) -> (ArrayVec<T, M>, ArrayVec<T, M>) {
    let mid = arr.len() / 2;
    match to_insert.cmp(&mid) {
        Ordering::Less => {
            let mid = mid - 1;
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid..));

            let mut left = arr;
            left.insert(to_insert, data);

            (left, right)
        }
        Ordering::Equal => {
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid..));

            let mut left = arr;
            left.push(data);

            (left, right)
        }
        Ordering::Greater => {
            let mid = mid + 1;
            let mut right = ArrayVec::new();

            if mid <= arr.len() {
                right.extend(arr.drain(mid..));
                right.insert(to_insert - mid, data);
            } else {
                right.push(data)
            }

            let left = arr;

            (left, right)
        }
    }
}

impl<T: Eq + Ord, const M: usize> BTree<T, M>
where
    [(); M + 1]:,
{
    pub fn search(&self, data: &T) -> Option<()> {
        match self.data.binary_search(data) {
            Ok(_) => Some(()),
            Err(i) => {
                if self.children.len() > 0 {
                    self.children[i].search(data)
                } else {
                    None
                }
            }
        }
    }

    fn split(&mut self, to_insert: usize, data: T, child: Option<Box<Node<T, M>>>) {
        let arr = mem::replace(&mut self.data, ArrayVec::new());
        let (left, new_data, right) = split(arr, to_insert, data);
        self.data.push(new_data);

        let (left, right) = if !self.children.is_empty() {
            let mut children = mem::replace(&mut self.children, ArrayVec::new());
            let (left_children, right_children) = if let Some(child) = child {
                split_children(children, to_insert + 1, child)
            } else {
                let mut right = ArrayVec::new();

                right.extend(children.drain(children.len() / 2 + 1..));

                (children, right)
            };

            let left = Node::Internal(BTree {
                data: left,
                children: left_children,
            });
            let right = Node::Internal(BTree {
                data: right,
                children: right_children,
            });

            (left, right)
        } else {
            let left = Node::Leaf(left);
            let right = Node::Leaf(right);

            (left, right)
        };

        self.children.push(Box::new(left));
        self.children.push(Box::new(right))
    }

    pub fn insert(&mut self, data: T) -> Option<T> {
        match self.data.binary_search(&data) {
            Ok(i) => Some(mem::replace(&mut self.data[i], data)),
            Err(i) => {
                if !self.children.is_empty() {
                    let (ret, up) = self.children[i].insert(data);
                    if let Some((data, child)) = up {
                        if self.data.is_full() {
                            self.split(i, data, Some(child))
                        } else {
                            self.data.insert(i, data);
                            self.children.insert(i + 1, child)
                        }
                    };

                    ret
                } else {
                    if self.data.is_full() {
                        self.split(i, data, None)
                    } else {
                        self.data.insert(i, data);
                    }

                    None
                }
            }
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        None
    }
}

impl<T: Eq + Ord, const M: usize> Node<T, M>
where
    [(); M + 1]:,
{
    fn search(&self, data: &T) -> Option<()> {
        match self {
            Node::Internal(intl) => match intl.data.binary_search(data) {
                Ok(_) => Some(()),
                Err(i) => intl.children[i].search(data),
            },
            Node::Leaf(l) => match l.binary_search(data) {
                Ok(_) => Some(()),
                Err(_) => None,
            },
        }
    }

    fn insert(&mut self, data: T) -> (Option<T>, Option<(T, Box<Node<T, M>>)>) {
        match self {
            Node::Internal(intl) => match intl.data.binary_search(&data) {
                Ok(i) => (Some(mem::replace(&mut intl.data[i], data)), None),
                Err(i) => {
                    let (ret, up) = intl.children[i].insert(data);

                    let up = if let Some((data, child)) = up {
                        if intl.data.is_full() {
                            let arr = mem::replace(&mut intl.data, ArrayVec::new());
                            let (left, new_data, right) = split(arr, i, data);

                            let children = mem::replace(&mut intl.children, ArrayVec::new());
                            let (left_children, right_children) =
                                split_children(children, i + 1, child);

                            let right = Box::new(Node::Internal(BTree {
                                data: right,
                                children: right_children,
                            }));
                            let left = BTree {
                                data: left,
                                children: left_children,
                            };

                            *intl = left;

                            Some((new_data, right))
                        } else {
                            intl.data.insert(i, data);
                            intl.children.insert(i + 1, child);

                            None
                        }
                    } else {
                        None
                    };

                    (ret, up)
                }
            },
            Node::Leaf(l) => match l.binary_search(&data) {
                Ok(i) => (Some(mem::replace(&mut l[i], data)), None),
                Err(i) => {
                    let up = if l.is_full() {
                        let arr = mem::replace(l, ArrayVec::new());
                        let (left, mid, right) = split(arr, i, data);

                        *l = left;

                        Some((mid, Box::new(Node::Leaf(right))))
                    } else {
                        l.insert(i, data);

                        None
                    };

                    (None, up)
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BTree, Node};

    impl<T: Eq + Ord, const M: usize> Node<T, M>
    where
        [(); M + 1]:,
    {
        fn check(&self, min: Option<&T>, max: Option<&T>) {
            match self {
                Node::Internal(intl) => {
                    assert_eq!(intl.data.len() + 1, intl.children.len());
                    assert!(intl.data.len() >= M / 2);

                    for i in 0..intl.data.len() - 1 {
                        assert!(intl.data[i] < intl.data[i + 1]);

                        if intl.children.len() > i {
                            let min = if i == 0 {
                                None
                            } else {
                                Some(&intl.data[i - 1])
                            };
                            let max = Some(&intl.data[i]);

                            intl.children[i].check(min, max)
                        }
                    }

                    if let Some(last) = intl.children.last() {
                        last.check(intl.data.last(), None)
                    }

                    if let Some(min) = min {
                        assert!(min < &intl.data[0])
                    }

                    if let Some(max) = max {
                        assert!(max > intl.data.last().unwrap())
                    }
                }
                Node::Leaf(l) => {
                    for i in 0..l.len() - 1 {
                        assert!(l[i] < l[i + 1])
                    }

                    if let Some(min) = min {
                        assert!(min < &l[0])
                    }

                    if let Some(max) = max {
                        assert!(max > l.last().unwrap())
                    }
                }
            }
        }
    }

    impl<T: Eq + Ord, const M: usize> BTree<T, M>
    where
        [(); M + 1]:,
    {
        fn check(&self) {
            assert!(self.children.len() == 0 || self.children.len() == self.data.len() + 1);

            for i in 0..self.data.len() - 1 {
                assert!(self.data[i] < self.data[i + 1]);

                if !self.children.is_empty() {
                    let min = if i == 0 {
                        None
                    } else {
                        Some(&self.data[i - 1])
                    };
                    let max = Some(&self.data[i]);

                    self.children[i].check(min, max)
                }
            }

            if let Some(last) = self.children.last() {
                last.check(self.data.last(), None)
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

        let mut tree = BTree::<_, 6>::new();
        tree.insert(3);
        tree.insert(6);
        tree.insert(7);
        tree.insert(4);
        tree.insert(5);
        tree.insert(2);
        tree.insert(1);

        tree.check();

        assert_eq!(tree.search(&1), Some(()));
    }

    #[test]
    fn leaf_split() {
        let mut tree = BTree::<_, 5>::new();
        tree.insert(3);
        tree.insert(6);
        tree.insert(4);
        tree.insert(5);
        tree.insert(2);
        tree.insert(1);
        tree.insert(7);
        tree.insert(8);
        tree.insert(9);

        tree.check();

        assert_eq!(tree.search(&9), Some(()));
    }

    #[test]
    fn many_split() {
        let mut tree = BTree::<_, 2>::new();

        for i in 0..32 {
            tree.insert(i);
            tree.check();
        }

        assert_eq!(tree.search(&9), Some(()));

        let mut tree = BTree::<_, 2>::new();

        for i in (0..32).rev() {
            tree.insert(i);
            tree.check();
        }

        assert_eq!(tree.search(&9), Some(()));
    }
}
