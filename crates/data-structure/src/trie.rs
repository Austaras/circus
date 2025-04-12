use std::{
    collections::{hash_map::Entry, HashMap},
    mem,
};

#[derive(Debug)]
pub struct Trie {
    node: Option<TreeNode>,
}

#[derive(Debug)]
enum TreeNode {
    Single(SingleNode),
    Multi(MultiNode),
}

#[derive(Debug)]
struct SingleNode {
    offset: usize,
    str: String,
}

#[derive(Debug)]
struct MultiNode {
    default: Option<String>,
    map: HashMap<char, TreeNode>,
}

impl Trie {
    pub fn new() -> Self {
        Self { node: None }
    }

    pub fn insert(&mut self, data: String) -> Option<String> {
        if let Some(node) = &mut self.node {
            node.insert(SingleNode {
                str: data,
                offset: 0,
            })
        } else {
            self.node = Some(TreeNode::Single(SingleNode {
                offset: 0,
                str: data,
            }));
            None
        }
    }

    pub fn search(&self, data: &str) -> Option<()> {
        if let Some(node) = &self.node {
            node.search(data)
        } else {
            None
        }
    }
}

impl TreeNode {
    fn insert(&mut self, data: SingleNode) -> Option<String> {
        match self {
            TreeNode::Single(s) => {
                if s.str[data.offset..] == data.str[data.offset..] {
                    let prev = mem::replace(s, data);

                    Some(prev.str)
                } else {
                    let prev = mem::replace(
                        s,
                        SingleNode {
                            offset: 0,
                            str: String::new(),
                        },
                    );

                    let mut m = MultiNode {
                        default: None,
                        map: HashMap::new(),
                    };

                    m.insert(prev);
                    let r = m.insert(data);

                    *self = TreeNode::Multi(m);

                    r
                }
            }
            TreeNode::Multi(m) => m.insert(data),
        }
    }

    fn search(&self, key: &str) -> Option<()> {
        match self {
            TreeNode::Single(s) => {
                if &s.str[s.offset..] == key {
                    Some(())
                } else {
                    None
                }
            }
            TreeNode::Multi(m) => {
                if let Some(k) = key.chars().next() {
                    if let Some(n) = m.map.get(&k) {
                        n.search(&key[1..])
                    } else {
                        None
                    }
                } else {
                    m.default.as_ref().map(|_| ())
                }
            }
        }
    }
}

impl MultiNode {
    fn insert(&mut self, mut data: SingleNode) -> Option<String> {
        if let Some(key) = data.str.chars().nth(data.offset) {
            data.offset += 1;
            match self.map.entry(key) {
                Entry::Occupied(mut o) => o.get_mut().insert(data),

                Entry::Vacant(v) => {
                    v.insert(TreeNode::Single(data));
                    None
                }
            }
        } else {
            match &mut self.default {
                Some(prev) => Some(mem::replace(prev, data.str)),

                None => {
                    self.default = Some(data.str);
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Trie;

    #[test]
    fn basic() {
        let mut tree = Trie::new();

        tree.insert(String::from("aaa"));
        tree.insert(String::from("bbb"));
        tree.insert(String::from("ccc"));

        assert_eq!(tree.search("aaa"), Some(()));
        assert_eq!(tree.search("ddd"), None);
    }

    #[test]
    fn common_prefix() {
        let mut tree = Trie::new();

        tree.insert(String::from("abc"));
        tree.insert(String::from("a"));
        tree.insert(String::from("abcd"));

        assert_eq!(tree.search("abc"), Some(()));
        assert_eq!(tree.search("a"), Some(()));
        assert_eq!(tree.search("abcde"), None);
    }
}
