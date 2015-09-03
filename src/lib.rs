use std::borrow::Borrow;
use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::Index;
use std::sync::RwLock;

pub struct ShardHashMap<K, V> {
    shards: Vec<RwLock<HashMap<K, V>>>,
}

pub struct Keys<'a, K: 'a, V> { k: PhantomData<&'a K>, v: PhantomData<V>, }
pub struct Values<'a, K: 'a, V> { k: PhantomData<&'a K>, v: PhantomData<V>, }
pub struct Entry<K, V> { k: PhantomData<K>, v: PhantomData<V>, }
pub struct Drain<K, V> { k: PhantomData<K>, v: PhantomData<V>, }

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
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> { unimplemented!(); }
    pub fn values<'a>(&'a self) -> Values<'a, K, V> { unimplemented!(); }
    pub fn iter(&self) -> Iter<K, V> { unimplemented!(); }
    pub fn iter_mut(&mut self) -> IterMut<K, V> { unimplemented!(); }
    pub fn entry(&mut self, key: K) -> Entry<K, V> { unimplemented!(); }
    pub fn len(&self) -> usize { unimplemented!(); }
    pub fn is_empty(&self) -> bool { unimplemented!(); }
    pub fn drain(&mut self) -> Drain<K, V> { unimplemented!(); }
    pub fn clear(&mut self) { unimplemented!(); }
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V> where K: Borrow<Q>, Q: Hash + Eq { unimplemented!(); }
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool where K: Borrow<Q>, Q: Hash + Eq { unimplemented!(); }
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V> where K: Borrow<Q>, Q: Hash + Eq { unimplemented!(); }
    pub fn insert(&mut self, k: K, v: V) -> Option<V> { unimplemented!(); }
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V> where K: Borrow<Q>, Q: Hash + Eq { unimplemented!(); }
}

impl<K, V> PartialEq for ShardHashMap<K, V> where K: Eq + Hash, V: PartialEq {
    fn eq(&self, other: &ShardHashMap<K, V>) -> bool {
        unimplemented!();
    }
}

impl<K, V> Eq for ShardHashMap<K, V> where K: Eq + Hash, V: Eq {}

impl<K, V> Debug for ShardHashMap<K, V> where K: Eq + Hash + Debug, V: Debug {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        unimplemented!();
    }
}

impl<'a, K, V> IntoIterator for &'a ShardHashMap<K, V> where K: Eq + Hash {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        unimplemented!();
    }
}

impl<'a, K, V> IntoIterator for &'a mut ShardHashMap<K, V> where K: Eq + Hash {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        unimplemented!();
    }
}

impl<'a, K, V> IntoIterator for ShardHashMap<K, V> where K: Eq + Hash {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> IntoIter<K, V> {
        unimplemented!();
    }
}

impl<'a, K, Q: ?Sized, V> Index<&'a Q> for ShardHashMap<K, V> where K: Eq + Hash + Borrow<Q>, Q: Eq + Hash {
    type Output = V;

    fn index(&self, index: &Q) -> &V {
        unimplemented!();
    }
}

impl<K, V> FromIterator<(K, V)> for ShardHashMap<K, V> where K: Eq + Hash {
    fn from_iter<T: IntoIterator<Item=(K, V)>>(iterable: T) -> ShardHashMap<K, V> {
        unimplemented!();
    }
}

impl<K, V> Extend<(K, V)> for ShardHashMap<K, V> where K: Eq + Hash {
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        unimplemented!();
    }
}

impl<'a, K, V> Extend<(&'a K, &'a V)> for ShardHashMap<K, V> where K: Eq + Hash + Copy, V: Copy {
    fn extend<T: IntoIterator<Item=(&'a K, &'a V)>>(&mut self, iter: T) {
        unimplemented!();
    }
}

impl<K, V> Clone for ShardHashMap<K, V> {
    fn clone(&self) -> ShardHashMap<K, V> {
        unimplemented!();
    }
    fn clone_from(&mut self, source: &Self) {
        unimplemented!();
    }
}

pub struct Iter<'a, K: 'a, V> { k: PhantomData<&'a K>, v: PhantomData<V>, }

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        unimplemented!();
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        unimplemented!();
    }
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> {
        unimplemented!();
    }
    fn clone_from(&mut self, source: &Self) {
        unimplemented!();
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        unimplemented!();
    }
}

pub struct IterMut<'a, K: 'a, V> { k: PhantomData<&'a K>, v: PhantomData<V>, }

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        unimplemented!();
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        unimplemented!();
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize {
        unimplemented!();
    }
}

pub struct IntoIter<K, V> { k: PhantomData<K>, v: PhantomData<V>, }

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<(K, V)> {
        unimplemented!();
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        unimplemented!();
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        unimplemented!();
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
