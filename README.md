# Halo2 Learning Group Repo

Go to https://learn.0xparc.org/halo2 to follow along.

```
cargo build
cargo test --all-features -- --nocapture print
```

I recommend strating at fib_lec1.rs, which is amply marked up. To understand what each component is, you can read my notes on [halo2 here](https://www.remnote.com/a/halo2-notes/63c6758305f78c10a175b0c5) or even better if you have extra time, go through the source lectures from 0xPARC, [starting here](https://learn.0xparc.org/materials/halo2/learning-group-1/introduction).

## VSCode Setup

Add this to your settings.json:

```
"rust-analyzer.runnables.extraArgs": ["--all-features", "--release"]
```
