/// Traits to map between C structs and native Rust types.
/// Similar to glib-rs but a bit simpler and possibly more
/// idiomatic.
use libc::c_char;
use std::ffi::{c_void, CStr, CString};
use std::marker::PhantomData;
use std::ptr;

/// A type for which there is a canonical representation as a C datum.
pub trait CloneToForeign {
    /// The representation of `Self` as a C datum.  Typically a
    /// `struct`, though there are exceptions for example `c_char`
    /// for strings, since C strings are of `char *` type).
    type Foreign;

    /// Free the C datum pointed to by `p`.
    ///
    /// # Safety
    ///
    /// `p` must be `NULL` or point to valid data.
    ///
    /// ```
    /// # use rust_ptr::CloneToForeign;
    /// let s = "Hello, world!".to_string();
    /// let foreign = s.clone_to_foreign();
    /// unsafe {
    ///     String::free_foreign(foreign);
    /// }
    /// ```
    unsafe fn free_foreign(p: *mut Self::Foreign);

    /// Convert a native Rust object to a foreign C struct, copying
    /// everything pointed to by `self` (same as `to_glib_full` in `glib-rs`)
    fn clone_to_foreign(&self) -> *mut Self::Foreign;
}

/// A type which can be constructed from a canonical representation as a
/// C datum.
pub trait FromForeign: CloneToForeign + Sized {
    /// Convert a C datum to a native Rust object, copying everything
    /// pointed to by `self` (same as `from_glib_none` in `glib-rs`)
    ///
    /// # Safety
    ///
    /// `p` must point to valid data, or it can be `NULL` is `Self`
    /// is an `Option` type.
    ///
    /// ```
    /// # use rust_ptr::FromForeign;
    /// let p = b"Hello, world!\0".as_ptr();
    /// let s = unsafe {
    ///     String::cloned_from_foreign(p as *const libc::c_char)
    /// };
    /// assert_eq!(s, "Hello, world!");
    /// ```
    unsafe fn cloned_from_foreign(p: *const Self::Foreign) -> Self;

    /// Convert a C datum to a native Rust object, taking ownership of
    /// the pointer or Rust object (same as `from_glib_full` in `glib-rs`)
    ///
    /// The default implementation calls `cloned_from_foreign` and frees `p`.
    ///
    /// # Safety
    ///
    /// `p` must point to valid data, or it can be `NULL` is `Self` is an
    /// `Option` type.  `p` becomes invalid after the function returns.
    ///
    /// ```
    /// # use rust_ptr::{CloneToForeign, FromForeign};
    /// let s = "Hello, world!";
    /// let foreign = s.clone_to_foreign();
    /// unsafe {
    ///     assert_eq!(String::from_foreign(foreign), s);
    /// }
    /// // foreign is not leaked
    /// ```
    unsafe fn from_foreign(p: *mut Self::Foreign) -> Self {
        let result = Self::cloned_from_foreign(p);
        Self::free_foreign(p);
        result
    }
}

impl<T> CloneToForeign for Option<T>
where
    T: CloneToForeign,
{
    type Foreign = <T as CloneToForeign>::Foreign;

    unsafe fn free_foreign(x: *mut Self::Foreign) {
        T::free_foreign(x)
    }

    fn clone_to_foreign(&self) -> *mut Self::Foreign {
        // Same as the underlying implementation, but also convert `None`
        // to a `NULL` pointer.
        self.as_ref()
            .map(|x| x.clone_to_foreign())
            .unwrap_or(ptr::null_mut())
    }
}

impl<T> FromForeign for Option<T>
where
    T: FromForeign,
{
    unsafe fn cloned_from_foreign(p: *const Self::Foreign) -> Self {
        // Same as the underlying implementation, but also accept a `NULL` pointer.
        p.as_ref().map(|x| T::cloned_from_foreign(x))
    }
}

impl<T> CloneToForeign for Box<T>
where
    T: CloneToForeign,
{
    type Foreign = <T as CloneToForeign>::Foreign;

    unsafe fn free_foreign(x: *mut Self::Foreign) {
        T::free_foreign(x)
    }

    fn clone_to_foreign(&self) -> *mut Self::Foreign {
        self.as_ref().clone_to_foreign()
    }
}

impl<T> FromForeign for Box<T>
where
    T: FromForeign,
{
    unsafe fn cloned_from_foreign(p: *const Self::Foreign) -> Self {
        Box::new(T::cloned_from_foreign(p))
    }
}

/// Convert a C datum into a native Rust object, taking ownership of
/// the C datum.  You should not need to implement this trait
/// as long as Rust types implement `FromForeign`.
pub trait IntoNative<T> {
    /// Convert a C datum to a native Rust object, taking ownership of
    /// the pointer or Rust object (same as `from_glib_full` in `glib-rs`)
    ///
    /// # Safety
    ///
    /// `p` must be `NULL` or point to valid data, and becomes
    /// invalid after the function returns.
    ///
    /// ```
    /// # use rust_ptr::{CloneToForeign, IntoNative};
    /// let s = "Hello, world!".to_string();
    /// let foreign = s.clone_to_foreign();
    /// let native: String = unsafe {
    ///     foreign.into_native()
    ///     // foreign is not leaked
    /// };
    /// assert_eq!(s, native);
    /// ```
    unsafe fn into_native(self) -> T;
}

impl<T, U> IntoNative<U> for *mut T
where
    U: FromForeign<Foreign = T>,
{
    unsafe fn into_native(self) -> U {
        U::from_foreign(self)
    }
}

/// A pointer whose contents were borrowed from a Rust object, and
/// therefore whose lifetime is limited to the lifetime of the
/// underlying Rust object.  The Rust object was borrowed from a
/// shared reference, and therefore the pointer is not mutable.
pub struct BorrowedPointer<'a, P, T: 'a> {
    ptr: *const P,
    storage: T,
    _marker: PhantomData<&'a P>,
}

impl<'a, P, T: 'a> BorrowedPointer<'a, P, T> {
    /// Return a new `BorrowedPointer` that wraps the pointer `ptr`.
    /// `storage` can contain any other data that `ptr` points to,
    /// and that should be dropped when the `BorrowedPointer` goes out
    /// of scope.
    pub fn new(ptr: *const P, storage: T) -> Self {
        BorrowedPointer {
            ptr,
            storage,
            _marker: PhantomData,
        }
    }

    /// Return the pointer that is stored in the `BorrowedPointer`.  The
    /// pointer is valid for as long as the `BorrowedPointer` itself.
    ///
    /// ```
    /// # use rust_ptr::ForeignBorrow;
    /// let s = "Hello, world!".to_string();
    /// let borrowed = s.borrow_foreign();
    /// let len = unsafe { libc::strlen(borrowed.as_ptr()) };
    /// # assert_eq!(len, 13);
    /// ```
    pub fn as_ptr(&self) -> *const P {
        self.ptr
    }

    fn map<U: 'a, F: FnOnce(T) -> U>(self, f: F) -> BorrowedPointer<'a, P, U> {
        BorrowedPointer {
            ptr: self.ptr,
            storage: f(self.storage),
            _marker: PhantomData,
        }
    }
}

impl<'a, P, T: 'a> Debug for BorrowedPointer<'a, P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ptr_name = std::any::type_name::<*mut P>();
        let storage_name = std::any::type_name::<T>();
        let name = format!("BorrowedPointer<{}, {}>", ptr_name, storage_name);
        f.debug_tuple(&name).field(&self.as_ptr()).finish()
    }
}

/// A pointer whose contents were borrowed from a Rust object, and
/// therefore whose lifetime is limited to the lifetime of the
/// underlying Rust object.  The Rust object is borrowed from an
/// exclusive reference, and therefore the pointer is mutable.
pub struct BorrowedMutPointer<'a, P, T: 'a> {
    ptr: *mut P,
    storage: T,
    _marker: PhantomData<&'a P>,
}

impl<'a, P, T: 'a> BorrowedMutPointer<'a, P, T> {
    /// Return a new `BorrowedMutPointer` that wraps the pointer `ptr`.
    /// `storage` can contain any other data that `ptr` points to,
    /// and that should be dropped when the `BorrowedMutPointer` goes out
    /// of scope.
    pub fn new(ptr: *mut P, storage: T) -> Self {
        BorrowedMutPointer {
            ptr,
            storage,
            _marker: PhantomData,
        }
    }

    /// Return the pointer that is stored in the `BorrowedPointer`.  The
    /// returned pointer is constant and is valid for as long as the
    /// `BorrowedPointer` itself.
    pub fn as_ptr(&self) -> *const P {
        self.ptr
    }

    /// Return the pointer that is stored in the `BorrowedPointer`.  The
    /// returned pointer is mutable and is valid for as long as the
    /// `BorrowedPointer` itself.
    pub fn as_mut_ptr(&mut self) -> *mut P {
        self.ptr
    }

    fn map<U: 'a, F: FnOnce(T) -> U>(self, f: F) -> BorrowedMutPointer<'a, P, U> {
        BorrowedMutPointer {
            ptr: self.ptr,
            storage: f(self.storage),
            _marker: PhantomData,
        }
    }
}

impl<'a, P, T: 'a> Debug for BorrowedMutPointer<'a, P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = std::any::type_name::<*mut P>();
        let name = format!("BorrowedMutPointer<{}>", name);
        f.debug_tuple(&name).field(&self.as_ptr()).finish()
    }
}

/// A type for which a C representation can be borrowed without cloning.
pub trait ForeignBorrow<'a>: CloneToForeign {
    /// The type of any extra data that are needed while the `BorrowedPointer` is alive.
    type Storage: 'a;

    /// Return a wrapper for a C representation of `self`.  The wrapper
    /// allows access via a constant pointer.
    ///
    /// ```
    /// # use rust_ptr::ForeignBorrow;
    /// let s = "Hello, world!".to_string();
    /// let borrowed = s.borrow_foreign();
    /// let len = unsafe { libc::strlen(borrowed.as_ptr()) };
    /// # assert_eq!(len, 13);
    /// ```
    fn borrow_foreign(&'a self) -> BorrowedPointer<'a, Self::Foreign, Self::Storage>;
}

impl<'a, T> ForeignBorrow<'a> for Option<T>
where
    T: ForeignBorrow<'a>,
{
    type Storage = Option<<T as ForeignBorrow<'a>>::Storage>;

    fn borrow_foreign(&'a self) -> BorrowedPointer<'a, Self::Foreign, Self::Storage> {
        match self.as_ref().map(|x| x.borrow_foreign()) {
            None => BorrowedPointer::new(ptr::null(), None),
            Some(bp) => bp.map(Some),
        }
    }
}

impl<'a, T> ForeignBorrow<'a> for Box<T>
where
    T: ForeignBorrow<'a>,
{
    type Storage = <T as ForeignBorrow<'a>>::Storage;

    fn borrow_foreign(&'a self) -> BorrowedPointer<'a, Self::Foreign, Self::Storage> {
        self.as_ref().borrow_foreign()
    }
}

/// A type for which a C representation can be borrowed mutably without cloning.
pub trait ForeignBorrowMut<'a>: CloneToForeign {
    /// The type of any extra data that are needed while the `BorrowedPointer` is alive.
    type Storage: 'a;

    /// Return a wrapper for a C representation of `self`.  The wrapper
    /// allows access via a mutable pointer.
    fn borrow_foreign_mut(&'a mut self) -> BorrowedMutPointer<'a, Self::Foreign, Self::Storage>;
}

impl<'a, T> ForeignBorrowMut<'a> for Option<T>
where
    T: ForeignBorrowMut<'a>,
{
    type Storage = Option<<T as ForeignBorrowMut<'a>>::Storage>;

    fn borrow_foreign_mut(&'a mut self) -> BorrowedMutPointer<'a, T::Foreign, Self::Storage> {
        match self.as_mut().map(|x| x.borrow_foreign_mut()) {
            None => BorrowedMutPointer::new(ptr::null_mut(), None),
            Some(bp) => bp.map(Some),
        }
    }
}

impl<'a, T> ForeignBorrowMut<'a> for Box<T>
where
    T: ForeignBorrowMut<'a>,
{
    type Storage = <T as ForeignBorrowMut<'a>>::Storage;

    fn borrow_foreign_mut(&'a mut self) -> BorrowedMutPointer<'a, Self::Foreign, Self::Storage> {
        self.as_mut().borrow_foreign_mut()
    }
}

impl CloneToForeign for str {
    type Foreign = c_char;

    unsafe fn free_foreign(ptr: *mut c_char) {
        libc::free(ptr as *mut c_void);
    }

    fn clone_to_foreign(&self) -> *mut c_char {
        // SAFETY: self.as_ptr() is guaranteed to point to self.len() bytes;
        // the destination is freshly allocated
        unsafe {
            let p = libc::malloc(self.len() + 1) as *mut c_char;
            ptr::copy_nonoverlapping(self.as_ptr() as *const c_char, p, self.len());
            *p.add(self.len()) = 0;
            p
        }
    }
}

impl CloneToForeign for String {
    type Foreign = c_char;

    unsafe fn free_foreign(ptr: *mut c_char) {
        libc::free(ptr as *mut c_void);
    }

    fn clone_to_foreign(&self) -> *mut c_char {
        // SAFETY: self.as_ptr() is guaranteed to point to self.len() bytes;
        // the destination is freshly allocated
        unsafe {
            let p = libc::malloc(self.len() + 1) as *mut c_char;
            ptr::copy_nonoverlapping(self.as_ptr() as *const c_char, p, self.len());
            *p.add(self.len()) = 0;
            p
        }
    }
}

impl FromForeign for String {
    unsafe fn cloned_from_foreign(p: *const c_char) -> Self {
        let cstr = CStr::from_ptr(p);
        String::from_utf8_lossy(cstr.to_bytes()).into_owned()
    }
}

impl ForeignBorrow<'_> for String {
    type Storage = CString;

    fn borrow_foreign(&self) -> BorrowedPointer<c_char, CString> {
        let tmp = CString::new(&self[..]).unwrap();
        BorrowedPointer::new(tmp.as_ptr(), tmp)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use matches::assert_matches;
    use std::ffi::c_void;

    #[test]
    fn test_borrow_foreign_string() {
        let s = "Hello, world!".to_string();
        let borrowed = s.borrow_foreign();
        unsafe {
            let len = libc::strlen(borrowed.as_ptr());
            assert_eq!(len, s.len());
            assert_eq!(
                libc::memcmp(
                    borrowed.as_ptr() as *const c_void,
                    "Hello, world!\0".as_bytes().as_ptr() as *const c_void,
                    len + 1
                ),
                0
            );
        }
    }

    #[test]
    fn test_cloned_from_foreign_string() {
        let s = "Hello, world!".to_string();
        let borrowed = s.borrow_foreign();
        let cloned = unsafe { String::cloned_from_foreign(s.borrow_foreign().as_ptr()) };
        assert_eq!(s, cloned);
        assert_ne!(s.borrow_foreign().as_ptr(), borrowed.as_ptr());
    }

    #[test]
    fn test_from_foreign_string() {
        let s = "Hello, world!".to_string();
        let cloned = s.clone_to_foreign();
        let copy = unsafe { String::from_foreign(cloned) };
        assert_eq!(s, copy);
    }

    #[test]
    fn test_clone_to_foreign_str() {
        let s = "Hello, world!";
        let p = b"Hello, world!\0".as_ptr();
        let cloned = s.clone_to_foreign();
        unsafe {
            let len = libc::strlen(cloned);
            assert_eq!(len, s.len());
            assert_eq!(
                libc::memcmp(cloned as *const c_void, p as *const c_void, len + 1),
                0
            );
            libc::free(cloned as *mut c_void);
        }
    }

    #[test]
    fn test_clone_to_foreign_string() {
        let s = "Hello, world!".to_string();
        let borrowed = s.borrow_foreign();
        let cloned = s.clone_to_foreign();
        assert_ne!(borrowed.as_ptr(), cloned);
        unsafe {
            let len = libc::strlen(cloned);
            assert_eq!(len, s.len());
            assert_eq!(
                libc::memcmp(
                    cloned as *const c_void,
                    borrowed.as_ptr() as *const c_void,
                    len + 1
                ),
                0
            );
            libc::free(cloned as *mut c_void);
        }
    }

    #[test]
    fn test_option() {
        // An Option can be used to produce or convert NULL pointers
        let s = Some("Hello, world!".to_string());
        unsafe {
            assert_eq!(
                String::cloned_from_foreign(s.borrow_foreign().as_ptr()),
                s.unwrap()
            )
        }
        let s: Option<String> = None;
        assert_eq!(s.borrow_foreign().as_ptr(), ptr::null());

        unsafe {
            assert_matches!(Option::<String>::cloned_from_foreign(ptr::null()), None);
            assert_matches!(Option::<String>::from_foreign(ptr::null_mut()), None);
        }
    }

    #[test]
    fn test_box() {
        // Contents of a Box can be borrowed, and a box can be produced if
        // the inner type can.
        let s = Box::new("Hello, world!".to_string());
        let borrowed = s.borrow_foreign();
        let cloned = unsafe { Box::<String>::cloned_from_foreign(borrowed.as_ptr()) };
        assert_eq!(s, cloned);

        let s = Some(Box::new("Hello, world!".to_string()));
        let borrowed = s.borrow_foreign();
        let cloned = unsafe { Option::<Box<String>>::cloned_from_foreign(borrowed.as_ptr()) };
        assert_eq!(s, cloned);
    }
}
