use std::{
    fmt::{Display, Write},
    mem,
};

pub struct BinaryHeap<T> {
    node: Vec<T>,
}

impl<T> BinaryHeap<T> {
    pub fn new() -> Self {
        Self { node: Vec::new() }
    }
}

impl<T: Display> Display for BinaryHeap<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut step = 1;

        let mut idx = 0;

        while idx < self.node.len() {
            let start = idx;

            while idx < start + step && idx < self.node.len() {
                self.node[idx].fmt(f)?;
                f.write_char(' ')?;
                idx += 1;
            }

            f.write_char('\n')?;

            step = step * 2;
        }

        Ok(())
    }
}

impl<T: Eq + Ord> BinaryHeap<T> {
    pub fn insert(&mut self, data: T) {
        self.node.push(data);

        self.up(self.node.len() - 1)
    }

    fn up(&mut self, idx: usize) {
        if idx > 0 && self.node[(idx - 1) / 2] > self.node[idx] {
            let parent = (idx - 1) / 2;
            self.node.swap(parent, idx);
            self.up(parent)
        }
    }

    fn down(&mut self, idx: usize) {
        let left = idx * 2 + 1;
        let right = idx * 2 + 2;
        let mut smallest = idx;

        if right < self.node.len() {
            if self.node[smallest] > self.node[right] {
                smallest = right;
            }
        }

        if left < self.node.len() {
            if self.node[smallest] > self.node[left] {
                smallest = left;
            }
        }

        if smallest > idx {
            self.node.swap(idx, smallest);
            self.down(smallest);
        }
    }

    pub fn extract(&mut self) -> Option<T> {
        let mut last = self.node.pop()?;

        if self.node.is_empty() {
            return Some(last);
        }

        mem::swap(&mut self.node[0], &mut last);

        self.down(0);

        Some(last)
    }

    pub fn replace(&mut self, mut data: T) -> T {
        if self.node.is_empty() || self.node[0] >= data {
            return data;
        }

        mem::swap(&mut data, &mut self.node[0]);

        self.down(0);

        data
    }

    pub fn search(&mut self, data: &T) -> Option<usize> {
        if self.node.is_empty() || &self.node[0] > data {
            return None;
        }

        let mut curr = Vec::new();

        curr.push(0 as usize);

        while !curr.is_empty() {
            let mut next = Vec::new();

            for n in curr {
                match self.node[n].cmp(data) {
                    std::cmp::Ordering::Less => {
                        if n * 2 + 2 < self.node.len() {
                            next.push(n * 2 + 2);
                        }

                        if n * 2 + 1 < self.node.len() {
                            next.push(n * 2 + 1)
                        }
                    }
                    std::cmp::Ordering::Equal => return Some(n),
                    std::cmp::Ordering::Greater => (),
                }
            }

            curr = next
        }

        None
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        let idx = self.search(data)?;
        let last = self.node.len() - 1;
        self.node.swap(idx, last);

        let data = self.node.pop()?;

        match self.node[idx].cmp(&data) {
            std::cmp::Ordering::Less => self.up(idx),
            std::cmp::Ordering::Equal => (),
            std::cmp::Ordering::Greater => self.down(idx),
        }

        Some(data)
    }

    fn restore(&mut self) {
        for idx in (0..self.node.len() / 2).rev() {
            self.down(idx);
        }
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        let mut heap = Self { node: vec };

        heap.restore();

        heap
    }

    pub fn merge(&mut self, other: Self) {
        self.node.extend(other.node);
        self.restore();
    }
}

#[cfg(test)]
mod tests {
    use super::BinaryHeap;

    impl<T: Eq + Ord> BinaryHeap<T> {
        fn check(&self) {
            let mut curr = Vec::new();

            if self.node.len() > 0 {
                curr.push(0 as usize);
            }

            while !curr.is_empty() {
                let mut next = Vec::new();

                for n in &curr {
                    let left = n * 2 + 1;

                    if left < self.node.len() {
                        assert!(self.node[*n] <= self.node[left]);
                        next.push(left)
                    }

                    let right = n * 2 + 2;

                    if right < self.node.len() {
                        assert!(self.node[*n] <= self.node[right]);
                        next.push(right)
                    }
                }

                curr = next;
            }
        }
    }

    #[test]
    fn basic() {
        let mut heap = BinaryHeap::new();
        heap.insert(1);
        heap.insert(3);
        heap.insert(5);
        heap.insert(7);

        heap.check();

        assert_eq!(&heap.node, &[1, 3, 5, 7]);
        assert_eq!(heap.search(&5), Some(2));
    }

    #[test]
    fn reverse() {
        let mut heap = BinaryHeap::new();
        heap.insert(7);
        heap.insert(5);
        heap.insert(3);
        heap.insert(1);

        heap.check();

        assert_eq!(&heap.node, &[1, 3, 5, 7]);
        assert_eq!(heap.search(&5), Some(2));
    }

    #[test]
    fn sort() {
        let mut heap = BinaryHeap::new();

        for i in [1, 0, 8, 6, 5, 2, 7, 3, 9, 4] {
            heap.insert(i);
        }

        heap.check();

        let mut sorted = Vec::new();

        while let Some(min) = heap.extract() {
            sorted.push(min);
        }

        assert_eq!(&sorted, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn duplicate() {
        let mut heap = BinaryHeap::new();

        for i in [1, 0, 8, 6, 5, 2, 7, 3, 9, 4, 3, 1, 3] {
            heap.insert(i);
        }

        heap.check();

        let mut sorted = Vec::new();

        while let Some(min) = heap.extract() {
            sorted.push(min);
        }

        assert_eq!(&sorted, &[0, 1, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn sort_delete() {
        let mut heap = BinaryHeap::new();

        for i in [1, 0, 8, 6, 5, 2, 7, 3, 9, 4] {
            heap.insert(i);
        }

        heap.check();

        heap.delete(&7);
        heap.delete(&5);

        let mut sorted = Vec::new();

        while let Some(min) = heap.extract() {
            sorted.push(min);
        }

        assert_eq!(&sorted, &[0, 1, 2, 3, 4, 6, 8, 9]);
    }

    #[test]
    fn from_vec() {
        let heap = BinaryHeap::from_vec(vec![1, 0, 8, 6, 5, 2, 7, 3, 9, 4]);

        heap.check();
    }
}
