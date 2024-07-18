use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Index, Range};

use indexmap::IndexSet;

/// The index of a value allocated in an arena that holds `T`s.
///
/// The Clone, Copy and other traits are defined manually because
/// deriving them adds some additional constraints on the `T` generic type
/// that we actually don't need since it is phantom.
///
/// <https://github.com/rust-lang/rust/issues/26925>
pub struct Id<T> {
    raw: u32,
    _ty: PhantomData<fn() -> T>,
}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Id<T> {}

impl<T> PartialEq for Id<T> {
    fn eq(&self, other: &Id<T>) -> bool {
        self.raw == other.raw
    }
}

impl<T> Eq for Id<T> {}

impl<T> Hash for Id<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state)
    }
}

impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut type_name = std::any::type_name::<T>();
        if let Some(id) = type_name.rfind(':') {
            type_name = &type_name[id + 1..]
        }
        write!(f, "Id::<{}>({})", type_name, self.raw)
    }
}

/// TODO: remove!
impl<T> fmt::Display for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut type_name = std::any::type_name::<T>();
        if let Some(id) = type_name.rfind(':') {
            type_name = &type_name[id + 1..]
        }
        write!(f, "Id::<{}>({})", type_name, self.raw)
    }
}

impl<T> Id<T> {
    pub fn into_raw(self) -> usize {
        self.raw as usize
    }
    fn from(n: u32) -> Self {
        Self {
            raw: n,
            _ty: PhantomData,
        }
    }
    pub fn range_to_iter(range: Range<Self>) -> impl Iterator<Item = Self> {
        let start = range.start.raw;
        let end = range.end.raw;
        (start..end).map(Self::from)
    }
}

/// Yet another index-based arena.
///
/// An arena is a kind of simple grow-only allocator, backed by a `Vec`
/// where all items have the same lifetime, making it easier
/// to have references between those items.
/// They are all dropped at once when the arena is dropped.
#[derive(Clone, PartialEq, Eq)]
pub struct Arena<T> {
    data: Vec<T>,
}

impl<T: fmt::Debug> fmt::Debug for Arena<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Arena")
            .field("len", &self.data.len())
            .field("data", &self.data)
            .finish()
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    pub fn alloc(&mut self, value: T) -> Id<T> {
        let raw = self.data.len();
        self.data.push(value);
        Id::from(raw as u32)
    }

    pub fn alloc_iter<I: Iterator<Item = T>>(&mut self, values: I) -> Range<Id<T>> {
        let start = Id::from(self.data.len() as u32);
        values.for_each(|v| {
            self.alloc(v);
        });
        let end = Id::from(self.data.len() as u32);
        Range { start, end }
    }
}

impl<T> Index<Id<T>> for Arena<T> {
    type Output = T;
    fn index(&self, id: Id<T>) -> &T {
        &self.data[id.raw as usize]
    }
}

impl<T> Index<Range<Id<T>>> for Arena<T> {
    type Output = [T];
    fn index(&self, id: Range<Id<T>>) -> &[T] {
        &self.data[(id.start.raw as usize)..(id.end.raw as usize)]
    }
}

/// Yet another index-based arena. This one de-duplicates entries by hashing.
///
/// An arena is a kind of simple grow-only allocator, backed by a `Vec`
/// where all items have the same lifetime, making it easier
/// to have references between those items.
/// They are all dropped at once when the arena is dropped.
#[derive(Clone, PartialEq, Eq)]
pub struct HashArena<T: Hash + Eq> {
    data: IndexSet<T>,
}

impl<T: Hash + Eq + fmt::Debug> fmt::Debug for HashArena<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Arena")
            .field("len", &self.data.len())
            .field("data", &self.data)
            .finish()
    }
}

impl<T: Hash + Eq> HashArena<T> {
    pub fn new() -> Self {
        HashArena {
            data: IndexSet::new(),
        }
    }

    pub fn alloc(&mut self, value: T) -> Id<T> {
        let (raw, _) = self.data.insert_full(value);
        Id::from(raw as u32)
    }
}

impl<T: Hash + Eq> Index<Id<T>> for HashArena<T> {
    type Output = T;
    fn index(&self, id: Id<T>) -> &T {
        &self.data[id.raw as usize]
    }
}

#[derive(Clone, Debug)] // TODO
pub struct IdMap<K, V> {
    inner: Vec<Option<V>>,
    _ty: PhantomData<K>,
}

impl<K, V> IdMap<K, V> {
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            _ty: PhantomData,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (Id<K>, &V)> {
        self.inner
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.as_ref().map(|v| (Id::from(i as u32), v)))
    }

    pub fn get(&self, id: Id<K>) -> Option<&V> {
        self.inner.get(id.into_raw())?.as_ref()
    }

    pub fn get_mut(&mut self, id: Id<K>) -> Option<&mut V> {
        self.inner.get_mut(id.into_raw())?.as_mut()
    }

    pub fn take(&mut self, id: Id<K>) -> Option<V> {
        self.inner.get_mut(id.into_raw())?.take()
    }

    pub fn insert(&mut self, id: Id<K>, value: V) {
        for _ in self.inner.len()..=id.into_raw() {
            self.inner.push(None);
        }
        self.inner[id.into_raw()] = Some(value);
    }

    pub fn retain<F: FnMut(Id<K>, &mut V) -> bool>(&mut self, mut f: F) {
        self.inner.iter_mut().enumerate().for_each(|(i, v)| {
            if v.is_some() && !f(Id::from(i as u32), v.as_mut().unwrap()) {
                *v = None;
            }
        });
    }

    pub fn remove(&mut self, id: Id<K>) -> Option<V> {
        self.inner.get_mut(id.into_raw())?.take()
    }
}

impl<K, V: Default> IdMap<K, V> {
    pub fn get_or_defalt(&mut self, id: Id<K>) -> &mut V {
        for _ in self.inner.len()..=id.into_raw() {
            self.inner.push(None);
        }
        let out = &mut self.inner[id.into_raw()];
        if out.is_none() {
            *out = Some(V::default());
        }
        out.as_mut().unwrap()
    }
}

impl<K, V> Index<Id<K>> for IdMap<K, V> {
    type Output = V;
    fn index(&self, id: Id<K>) -> &V {
        self.inner[id.into_raw()].as_ref().unwrap()
    }
}

impl<K, V> Default for IdMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
