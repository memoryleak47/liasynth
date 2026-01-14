use crate::GLOBAL_STATS;
use dashmap::DashMap;
use once_cell::sync::Lazy;
use std::sync::Arc;
use std::sync::atomic::{
    AtomicBool, AtomicU64,
    Ordering::{Relaxed, SeqCst},
};
use std::time::Instant;

struct PhaseStats {
    ns: AtomicU64,
    count: AtomicU64,
}

static PHASES: Lazy<DashMap<&'static str, Arc<PhaseStats>>> = Lazy::new(DashMap::new);
static REPORTED: AtomicBool = AtomicBool::new(false);

pub struct PhaseTimer {
    name: &'static str,
    start: Instant,
}
impl PhaseTimer {
    #[inline]
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            start: Instant::now(),
        }
    }
}
impl Drop for PhaseTimer {
    fn drop(&mut self) {
        // Cast to u64 (ns) — good for centuries of runtime; fine for profiling.
        let ns = self.start.elapsed().as_nanos() as u64;
        let entry = PHASES
            .entry(self.name)
            .or_insert_with(|| {
                Arc::new(PhaseStats {
                    ns: AtomicU64::new(0),
                    count: AtomicU64::new(0),
                })
            })
            .clone();
        entry.ns.fetch_add(ns, Relaxed);
        entry.count.fetch_add(1, Relaxed);
    }
}

#[macro_export]
macro_rules! time_block {
    ($name:expr) => {
        let _phase_timer_guard = $crate::phase_timing::PhaseTimer::new($name);
    };
}

pub fn print_timing_report_once() {
    if REPORTED.swap(true, SeqCst) {
        return;
    }
    print_timing_report();
}

fn print_stats_once() {
    if let Ok(s) = GLOBAL_STATS.try_lock() {
        s.print();
    }
}

pub fn print_timing_report() {
    let mut rows: Vec<(&'static str, u64, u64)> = Vec::new();
    let mut total_ns: u128 = 0;

    for r in PHASES.iter() {
        let s = r.value();
        let ns = s.ns.load(Relaxed);
        let c = s.count.load(Relaxed);
        total_ns += ns as u128;
        rows.push((*r.key(), ns, c));
    }
    rows.sort_by_key(|(_, ns, _)| std::cmp::Reverse(*ns));

    eprintln!("\n== Phase timing ==");
    for (name, ns, c) in &rows {
        let ms = (*ns as f64) / 1_000_000.0;
        let pct = if total_ns == 0 {
            0.0
        } else {
            (*ns as f64) * 100.0 / (total_ns as f64)
        };
        eprintln!("{:>18}: {:>10.3} ms  {:>6.2} %  (n={})", name, ms, pct, c);
    }
    let total_ms = (total_ns as f64) / 1_000_000.0;
    eprintln!("{:>18}: {:>10.3} ms  {:>6.2} %", "TOTAL", total_ms, 100.0);
}

pub fn init_timing_hooks() {
    // Ctrl-C / SIGTERM printer
    std::thread::spawn(|| {
        use signal_hook::consts::{SIGINT, SIGTERM};
        let mut signals = signal_hook::iterator::Signals::new([SIGINT, SIGTERM]).expect("signals");
        for _ in signals.forever() {
            print_timing_report_once();
            print_stats_once();
            // Try to exit with 130 like shells do for SIGINT.
            std::process::exit(130);
        }
    });

    // Panic printer (then run the previous hook)
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        print_timing_report_once();
        print_stats_once();
        prev(info);
    }));
}

// Ensures report on normal program end (when main returns).
pub struct ReportOnDrop;
impl Drop for ReportOnDrop {
    fn drop(&mut self) {
        print_timing_report_once();
        print_stats_once();
    }
}
