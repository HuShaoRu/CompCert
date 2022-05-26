# CompCert on LoongArch

Not finished yet. Still remain `Admitted` in some proofs.

Not tested on LoongArch32.

## Usage

```bash
./configure loongarch64-linux
make all
make install
ccomp -c src.c
ccomp -S src.c
```
