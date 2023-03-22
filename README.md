# Testudo

[![Build and Test Testudo](https://github.com/cryptonetlab/testudo/actions/workflows/testudo.yml/badge.svg?branch=master)](https://github.com/cryptonetlab/testudo/actions/workflows/testudo.yml)

Testudo is a linear-time prover SNARK with a small and universal trusted setup. For a deep dive, please refer to [this](https://www.notion.so/pl-strflt/Testudo-Blog-Post-Final-a18db71f8e634ebbb9f68383f7904c51) blog post.

In the current stage, the repository contains:

- a modified version of [Spartan](https://github.com/microsoft/Spartan) using [arkworks](https://github.com/arkworks-rs) with the sumchecks verified using Groth16
- a fast version of the [PST](https://eprint.iacr.org/2011/587.pdf) commitment scheme with a square-root trusted setup
- support for an arkworks wrapper around the fast blst library with GPU integration [repo](https://github.com/nikkolasg/ark-blst)

## Building `testudo`

Testudo is available with stable Rust.

Run `cargo build` or `cargo test` to build, respectively test the repository.

To run the current benchmarks on BLS12-377:

```console
cargo bench --bench testudo --all-features release -- --nocapture
```

## Join us!

If you want to contribute, reach out to the Discord server of [cryptonet](https://discord.com/invite/CFnTSkVTCk).
