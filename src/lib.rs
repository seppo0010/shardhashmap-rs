use std::cmp::Eq;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::RwLock;

pub struct ShardHashMap<K, V> {
    shards: Vec<RwLock<HashMap<K, V>>>,
}

impl<K, V> ShardHashMap<K, V> where K: Eq + Hash {
    pub fn new(shards: usize) -> Self {
        ShardHashMap::with_capacity(shards, 0)
    }

    pub fn with_capacity(shards_count: usize, capacity: usize) -> Self {
        let mut shards = Vec::with_capacity(shards_count);
        for _ in 0..shards_count {
            shards.push(RwLock::new(HashMap::with_capacity(capacity / shards_count + 1)));
        }
        ShardHashMap {
            shards: shards,
        }
    }

    pub fn capacity(&self) -> usize {
        let mut capacity = 0;
        for s in self.shards.iter() {
            let shard = match s.read() {
                Ok(shard) => shard,
                Err(poison_err) => poison_err.into_inner(),
            };
            capacity += shard.capacity();
        }
        capacity
    }

    pub fn reserve(&self, additional: usize) {
        let r = additional / self.shards.len() + 1;
        for s in self.shards.iter() {
            let mut shard = match s.write() {
                Ok(shard) => shard,
                Err(poison_err) => poison_err.into_inner(),
            };
            shard.reserve(r)
        }
    }

    pub fn shrink_to_fit(&self) {
        for s in self.shards.iter() {
            let mut shard = match s.write() {
                Ok(shard) => shard,
                Err(poison_err) => poison_err.into_inner(),
            };
            shard.shrink_to_fit();
        }
    }
}

#[test]
fn capacity() {
    let hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.capacity() >= 10);

    let hm = ShardHashMap::<u8, u8>::with_capacity(10, 20);
    assert!(hm.capacity() >= 20);
}

#[test]
fn reserve() {
    let hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.capacity() >= 10);
    assert!(hm.capacity() < 1000);
    hm.reserve(990);
    assert!(hm.capacity() >= 1000);
}

#[test]
fn shrink_to_fit() {
    let hm = ShardHashMap::<u8, u8>::with_capacity(10, 1000);
    let pre = hm.capacity();
    assert!(pre >= 10);
    hm.shrink_to_fit();
    assert!(hm.capacity() < pre);
}
