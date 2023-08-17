#![feature(naked_functions)]
use std::{arch::asm, ptr};

const DEFAULT_STACK_SIZE: usize = 1024 * 1024 * 8;
const MAX_THREADS: usize = 4;
static mut RUNTIME: *mut Runtime = ptr::null_mut();

pub struct Runtime {
    threads: Vec<Thread>,
    current: usize,
}

#[derive(PartialEq, Eq, Debug)]
enum State {
    /// All work has been done, can be reused
    Available,
    Running,
    /// Has some work to do, waiting to be picked up
    Ready,
}

struct Thread {
    #[allow(dead_code)]
    id: usize,
    stack: Box<[u8; DEFAULT_STACK_SIZE]>,
    ctx: ThreadContext,
    state: State,
}

#[cfg(target_arch = "x86_64")]
#[derive(Debug, Default)]
#[repr(C)]
struct ThreadContext {
    rsp: u64,
    r15: u64,
    r14: u64,
    r13: u64,
    r12: u64,
    rbx: u64,
    rbp: u64,
}

#[cfg(target_arch = "aarch64")]
#[derive(Debug, Default)]
#[repr(C)]
struct ThreadContext {
    r4: u64,
    r5: u64,
    r6: u64,
    r7: u64,
    r8: u64,
    r9: u64,
    r10: u64,
    /// frame pointer
    r11: u64,
    /// stack pointer
    r13: u64,
}

impl Thread {
    fn new(id: usize) -> Self {
        Thread {
            id,
            stack: vec![0_u8; DEFAULT_STACK_SIZE]
                .into_boxed_slice()
                .try_into()
                .unwrap(),
            ctx: ThreadContext::default(),
            state: State::Available,
        }
    }
}

impl Runtime {
    pub fn new() -> Self {
        let base_thread = Thread {
            id: 0,
            stack: vec![0_u8; DEFAULT_STACK_SIZE]
                .into_boxed_slice()
                .try_into()
                .unwrap(),
            ctx: ThreadContext::default(),
            state: State::Running,
        };

        let mut threads = vec![base_thread];
        let mut available_threads: Vec<Thread> = (1..MAX_THREADS).map(Thread::new).collect();
        threads.append(&mut available_threads);

        Runtime {
            threads,
            current: 0,
        }
    }

    pub fn init(&self) {
        unsafe {
            RUNTIME = self as *const Runtime as *mut Runtime;
        }
    }

    pub fn run(&mut self) -> ! {
        while self.t_yield() {}
        std::process::exit(0);
    }

    fn t_return(&mut self) {
        if self.current != 0 {
            self.threads[self.current].state = State::Available;
            self.t_yield();
        }
    }

    #[inline(never)]
    fn t_yield(&mut self) -> bool {
        let mut pos = self.current;
        while self.threads[pos].state != State::Ready {
            pos += 1;
            if pos == self.threads.len() {
                pos = 0;
            }
            if pos == self.current {
                return false;
            }
        }

        if self.threads[self.current].state != State::Available {
            self.threads[self.current].state = State::Ready;
        }

        self.threads[pos].state = State::Running;
        let old_pos = self.current;
        self.current = pos;

        unsafe {
            let old: *mut ThreadContext = &mut self.threads[old_pos].ctx;
            let new: *const ThreadContext = &self.threads[pos].ctx;
            switch(old, new);
        }
        self.threads.is_empty()
    }

    pub fn spawn(&mut self, f: fn()) {
        let available = self
            .threads
            .iter_mut()
            .find(|t| t.state == State::Available)
            .expect("no available thread.");

        let size = DEFAULT_STACK_SIZE;
        unsafe {
            let s_ptr = available.stack.as_mut_ptr().add(size);
            // make sure stack bottom 16 byte aligned
            let s_ptr = (s_ptr as usize & !15) as *mut u8;
            std::ptr::write(s_ptr.offset(-16) as *mut u64, guard as u64);
            std::ptr::write(s_ptr.offset(-24) as *mut u64, skip as u64);
            std::ptr::write(s_ptr.offset(-32) as *mut u64, f as u64);
            #[cfg(target_arch = "x86_64")]
            {
                available.ctx.rsp = s_ptr.offset(-32) as u64;
            }
            #[cfg(target_arch = "aarch64")]
            {
                available.ctx.r13 = s_ptr.offset(-32) as u64;
            }
        }
        available.state = State::Ready;
    }
}

fn skip() {}

fn guard() {
    unsafe {
        (*RUNTIME).t_return();
    };
}

pub fn yield_thread() {
    unsafe {
        (*RUNTIME).t_yield();
    };
}

#[naked]
unsafe extern "C" fn switch(old: *mut ThreadContext, new: *const ThreadContext) {
    #[cfg(target_arch = "x86_64")]
    asm!(
        "mov [rdi + 0x00], rsp",
        "mov [rdi + 0x08], r15",
        "mov [rdi + 0x10], r14",
        "mov [rdi + 0x18], r13",
        "mov [rdi + 0x20], r12",
        "mov [rdi + 0x28], rbx",
        "mov [rdi + 0x30], rbp",
        "mov rsp, [rsi + 0x00]",
        "mov r15, [rsi + 0x08]",
        "mov r14, [rsi + 0x10]",
        "mov r13, [rsi + 0x18]",
        "mov r12, [rsi + 0x20]",
        "mov rbx, [rsi + 0x28]",
        "mov rbp, [rsi + 0x30]",
        "ret",
        options(noreturn)
    );
    #[cfg(target_arch = "aarch64")]
    asm!("ret", options(noreturn))
}
pub fn main() {
    let mut runtime = Runtime::new();
    runtime.init();
    runtime.spawn(|| {
        println!("THREAD 1 STARTING");
        let id = 1;
        for i in 0..5 {
            println!("thread: {} counter: {}", id, i);
            yield_thread();
        }
        println!("THREAD 1 FINISHED");
    });
    runtime.spawn(|| {
        println!("THREAD 2 STARTING");
        let id = 2;
        for i in 0..10 {
            println!("thread: {} counter: {}", id, i);
            yield_thread();
        }
        println!("THREAD 2 FINISHED");
    });
    runtime.run();
}
