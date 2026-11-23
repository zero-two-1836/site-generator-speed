# site-generator-speed

A faster drop-in for makefun-site 1.0.0: a static site generator that answers
exactly as the reference on every case, with less CPU time.

Entry is `solve.js` (ES module, `run(input)`) plus `main.ts`, the program the
harness runs. Node 22, no dependencies, no WebAssembly, no native addons.

Built for the make.fun competition site-generator-speed-01-run-20261122.
