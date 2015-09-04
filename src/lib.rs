extern crate md5;

use std::borrow::Borrow;
use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash,Hasher};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Index};
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

mod hasher;
use hasher::Md5Hasher;

macro_rules! hashmap_read {
    ($shm: expr, $k: expr) => {
        match $shm.shards[$shm.bucket_index($k)].read() {
            Ok(shard) => shard,
            Err(poison_err) => poison_err.into_inner(),
        }
    }
}

macro_rules! hashmap_write {
    ($shm: expr, $k: expr) => {
        match $shm.shards[$shm.bucket_index($k)].write() {
            Ok(shard) => shard,
            Err(poison_err) => poison_err.into_inner(),
        }
    }
}

pub struct BorrowedValue<'a, K: 'a, V: 'a> {
    guard: RwLockReadGuard<'a, HashMap<K, V>>,
    key: &'a K,
}

impl<'a, K: 'a + Eq + Hash, V: 'a> BorrowedValue<'a, K, V> {
    fn new(guard: RwLockReadGuard<'a, HashMap<K, V>>, key: &'a K) -> Option<Self> {
        if guard.contains_key(key) {
            Some(BorrowedValue { guard: guard, key: key })
        } else {
            None
        }
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a> Deref for BorrowedValue<'a, K, V> {
    type Target = V;

    fn deref<'b>(&'b self) -> &'b V {
        self.guard.get(self.key).unwrap()
    }
}

pub struct BorrowedMutValue<'a, K: 'a, V: 'a> {
    guard: RwLockWriteGuard<'a, HashMap<K, V>>,
    key: &'a K,
}

impl<'a, K: 'a + Eq + Hash, V: 'a> BorrowedMutValue<'a, K, V> {
    fn new(guard: RwLockWriteGuard<'a, HashMap<K, V>>, key: &'a K) -> Option<Self> {
        if guard.contains_key(key) {
            Some(BorrowedMutValue { guard: guard, key: key })
        } else {
            None
        }
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a> Deref for BorrowedMutValue<'a, K, V> {
    type Target = V;

    fn deref<'b>(&'b self) -> &'b V {
        self.guard.get(self.key).unwrap()
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a> DerefMut for BorrowedMutValue<'a, K, V> {
    fn deref_mut<'b>(&'b mut self) -> &'b mut V {
        self.guard.get_mut(self.key).unwrap()
    }
}

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

    pub fn len(&self) -> usize {
        let mut len = 0;
        for s in self.shards.iter() {
            let shard = match s.read() {
                Ok(shard) => shard,
                Err(poison_err) => poison_err.into_inner(),
            };
            len += shard.len();
        }
        len
    }

    fn bucket_index(&self, k: &K) -> usize {
        let mut bucket = Md5Hasher::new();
        k.hash(&mut bucket);
        (bucket.finish() as usize) % self.shards.len()
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        hashmap_write!(self, &k).insert(k, v)
    }

    pub fn get<'a>(&'a self, k: &'a K) -> Option<BorrowedValue<'a, K, V>> {
        let bucket = hashmap_read!(self, &k);
        BorrowedValue::new(bucket, k)
    }

    pub fn get_mut<'a>(&'a mut self, k: &'a K) -> Option<BorrowedMutValue<'a, K, V>> {
        let bucket = hashmap_write!(self, &*k);
        BorrowedMutValue::new(bucket, k)
    }

    pub fn is_empty(&self) -> bool {
        for s in self.shards.iter() {
            let shard = match s.read() {
                Ok(shard) => shard,
                Err(poison_err) => poison_err.into_inner(),
            };
            if !shard.is_empty() {
                return false
            }
        }
        true
    }

    pub fn clear(&mut self) {
        for s in self.shards.iter() {
            let mut shard = match s.write() {
                Ok(shard) => shard,
                Err(poison_err) => poison_err.into_inner(),
            };
            shard.clear();
        }
    }

    pub fn contains_key(&self, k: &K) -> bool {
        let bucket = hashmap_read!(self, k);
        bucket.contains_key(k)
    }

    pub fn remove(&mut self, k: &K) -> Option<V> {
        hashmap_write!(self, k).remove(k)
    }

    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> { unimplemented!(); }
    pub fn values<'a>(&'a self) -> Values<'a, K, V> { unimplemented!(); }
    pub fn iter(&self) -> Iter<K, V> { unimplemented!(); }
    pub fn iter_mut(&mut self) -> IterMut<K, V> { unimplemented!(); }
    pub fn entry(&mut self, key: K) -> Entry<K, V> { unimplemented!(); }
    pub fn drain(&mut self) -> Drain<K, V> { unimplemented!(); }
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

impl<'a, K: 'a, V: 'a> IntoIterator for &'a ShardHashMap<K, V> where K: Eq + Hash {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        unimplemented!();
    }
}

impl<'a, K: 'a, V: 'a> IntoIterator for &'a mut ShardHashMap<K, V> where K: Eq + Hash {
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
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K, V> Extend<(&'a K, &'a V)> for ShardHashMap<K, V> where K: Eq + Hash + Copy, V: Copy {
    fn extend<T: IntoIterator<Item=(&'a K, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(&key, &value)| (key, value)));
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

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        unimplemented!();
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        unimplemented!();
    }
}

impl<'a, K: 'a, V: 'a> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> {
        unimplemented!();
    }
    fn clone_from(&mut self, source: &Self) {
        unimplemented!();
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        unimplemented!();
    }
}

pub struct IterMut<'a, K: 'a, V> { k: PhantomData<&'a K>, v: PhantomData<V>, }

impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        unimplemented!();
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        unimplemented!();
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for IterMut<'a, K, V> {
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

#[test]
fn len() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert_eq!(hm.len(), 0);
    hm.insert(1, 1);
    assert_eq!(hm.len(), 1);
    hm.insert(2, 2);
    assert_eq!(hm.len(), 2);
}

#[test]
fn insert() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.insert(1, 1).is_none());
    assert_eq!(hm.insert(1, 2).unwrap(), 1);
    assert_eq!(hm.insert(1, 3).unwrap(), 2);
}

#[test]
fn get() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.insert(1, 1).is_none());
    let k = 1;
    assert_eq!(*hm.get(&k).unwrap(), 1);
}

#[test]
fn is_empty() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.is_empty());
    assert!(hm.insert(1, 1).is_none());
    assert!(!hm.is_empty());
}

#[test]
fn get_mut() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.insert(1, 1).is_none());
    let k = 1;
    {
        let mut v = hm.get_mut(&k).unwrap();
        *v = 2;
    }
    assert_eq!(*hm.get(&k).unwrap(), 2);
}

#[test]
fn contains_key() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.insert(1, 1).is_none());
    assert!(hm.contains_key(&1));
    assert!(!hm.contains_key(&2));
}

#[test]
fn remove() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    assert!(hm.insert(1, 1).is_none());
    assert_eq!(hm.remove(&1), Some(1));
    assert_eq!(hm.remove(&1), None);
    assert_eq!(hm.remove(&2), None);
}

#[test]
fn extend() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    hm.extend(vec![(1, 1)]);
    assert_eq!(hm.len(), 1);
    let k = 1;
    assert_eq!(*hm.get(&k).unwrap(), 1);
}

#[test]
fn extend2() {
    let mut hm = ShardHashMap::<u8, u8>::with_capacity(10, 10);
    hm.extend(vec![(&1, &1)]);
    assert_eq!(hm.len(), 1);
    let k = 1;
    assert_eq!(*hm.get(&k).unwrap(), 1);
}
