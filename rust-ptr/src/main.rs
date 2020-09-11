// Traits to map between C structs and native Rust types.
// Similar to glib-rs but a bit simpler and possibly more
// idiomatic.

use libc::size_t;
use std::borrow::{Borrow, BorrowMut};
use std::ffi::{c_void, CStr, CString};
use std::marker::PhantomData;
use std::os::raw::c_char;

// Map between C structs and native Rust types, taking ownership of
// the pointer or Rust object

trait FromForeign<T> {
    unsafe fn from_foreign(_: T) -> Self;
}
trait IntoNative<T> {
    unsafe fn into_native(self) -> T;
}
impl<T, U> IntoNative<U> for T
where
    U: FromForeign<T>,
{
    unsafe fn into_native(self) -> U {
        U::from_foreign(self)
    }
}

trait ToForeign<T> {
    fn to_foreign(&self) -> *mut T;
}

trait IntoForeign<T> {
    fn into_foreign(self) -> *mut T;
}

// Example:

impl FromForeign<*mut c_char> for String {
    // from_glib_full
    unsafe fn from_foreign(ptr: *mut c_char) -> Self {
        let res = Self::with_foreign(ptr);
        libc::free(ptr as *mut c_void);
        res
    }
}

impl ToForeign<c_char> for String {
    // to_glib_full
    fn to_foreign(&self) -> *mut c_char {
        unsafe { libc::strndup(self.as_ptr() as *const c_char, self.len() as size_t) }
    }
}

// Not a good idea, because into_foreign() should return
// a malloc-ed pointer instead.  from_foreign(s.into_foreign())
// would crash
#[cfg(broken)]
impl IntoForeign<c_char> for String {
    fn into_foreign(mut self) -> *mut c_char {
        self.push('\0');
        let ptr = self.as_ptr();
        std::mem::forget(self);
        ptr as *mut _
    }
}

// Map between C structs and native Rust types, borrowing
// the pointer or Rust object

pub struct BorrowedPointer<'a, P, T: 'a> {
    native: *const P,
    storage: T,
    _marker: PhantomData<&'a P>,
}

impl<'a, P: Copy, T: 'a> BorrowedPointer<'a, P, T> {
    fn new(native: *const P, storage: T) -> Self {
        BorrowedPointer {
            native,
            storage,
            _marker: PhantomData,
        }
    }

    fn as_ptr(&self) -> *const P {
        self.native
    }
}

impl<'a, P, T> Borrow<T> for BorrowedPointer<'a, P, T> {
    fn borrow(&self) -> &T {
        &self.storage
    }
}

pub struct BorrowedMutPointer<'a, P, T: 'a> {
    native: *mut P,
    storage: T,
    _marker: PhantomData<&'a P>,
}

#[allow(dead_code)]
impl<'a, P: Copy, T: 'a> BorrowedMutPointer<'a, P, T> {
    fn new(native: *mut P, storage: T) -> Self {
        BorrowedMutPointer {
            native,
            storage,
            _marker: PhantomData,
        }
    }

    fn as_ptr(&self) -> *const P {
        self.native
    }

    fn as_mut_ptr(&mut self) -> *mut P {
        self.native
    }
}

impl<'a, P, T> Borrow<T> for BorrowedMutPointer<'a, P, T> {
    fn borrow(&self) -> &T {
        &self.storage
    }
}

impl<'a, P, T> BorrowMut<T> for BorrowedMutPointer<'a, P, T> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut self.storage
    }
}

trait ForeignConvert<'a> {
    type Native: Copy;
    type Storage: 'a;

    unsafe fn with_foreign(p: *const Self::Native) -> Self;
    fn as_foreign(&'a self) -> BorrowedPointer<'a, Self::Native, Self::Storage>;
}

trait ForeignMutConvert<'a>: ForeignConvert<'a> {
    fn as_foreign_mut(&'a mut self) -> BorrowedMutPointer<'a, Self::Native, Self::Storage>;
}

// Example:

impl ForeignConvert<'_> for String {
    type Native = c_char;
    type Storage = CString;

    // from_glib_none
    unsafe fn with_foreign(p: *const c_char) -> Self {
        let cstr = CStr::from_ptr(p);
        String::from_utf8_lossy(cstr.to_bytes()).into_owned()
    }

    // to_glib_none
    fn as_foreign(&self) -> BorrowedPointer<c_char, CString> {
        let tmp = CString::new(&self[..]).unwrap();
        BorrowedPointer::new(tmp.as_ptr(), tmp)
    }
}

impl<'a, P, T> Drop for BorrowedPointer<'a, P, T> {
    fn drop(&mut self) {
        println!("\tDropping a borrowed pointer");
    }
}

fn main() {
    let s = "Hello, world!".to_string();

    {
        let borrowed = s.as_foreign();
        println!("A Rust String: {}", s);
        println!("Ownership not transferred: {}", unsafe {
            String::with_foreign(borrowed.as_ptr())
        });
        println!("Still a Rust String: {}", s);
    }

    unsafe {
        println!("Starting printf test");
        libc::printf("printf says %s\n\0".as_ptr() as *const c_char,
                     s.as_foreign().as_ptr());
        libc::printf("printf says %s\n\0".as_ptr() as *const c_char,
                     s.as_foreign().as_ptr());
        println!("Ending printf test");
    }

    println!("Created a copy: {}", unsafe {
        String::from_foreign(s.to_foreign())
    });

    {
        let foreign: *mut c_char = s.to_foreign();
        println!("Ownership transferred to C: {}", unsafe {
            String::with_foreign(foreign)
        });
        println!("Ownership transferred back: {}", unsafe {
            String::from_foreign(foreign)
        });
        println!("Trying to transfer again, will now crash with a double free!");
        println!("Huh, it worked? {}", unsafe {
            String::from_foreign(foreign)
        });
    }
}
