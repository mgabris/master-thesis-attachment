# C++ implementation of backtrack for Spritz
This directory contains C++ implementation of basic and special state backtrack for cipher Spritz. 

## Build
To build binaries, invoke

```bash
$ cmake ./ && make
```

## Usage
Each variant of backtrack comes with its own binary, accepts state file on stdin and needs 2 positional arguments.

```bash
Usage: ./backtrack [stop after state is found (0/1)] [verbosity]
```

Stop after state is found set to 0 forces backtrack to simulate estimate equations situation.

Verbosity 2 prints default statistics about test file.

# C++ implementácia prehľadávania pre šifru Spritz
Tento adresár obsahuje implementáciu jednoduchého prehľadávania a vylepšenia použitím špeciálneho stavu v C++ pre šifru Spritz.

## Kompilácia
Kód sa skompiluje príkazom

```bash
$ cmake ./ && make
```

## Použitie
Každý variant prehľadávania má samostatný binárny súbor. Na štandardnom vstupe očakáva súbor so stavmi a potrebuje 2 argumenty.

```bash
Usage: ./backtrack [stop after state is found (0/1)] [verbosity]
```

Prvý argument nastavený na 0 nastaví prehľadávanie tak, aby pokračovalo aj po nájdení správneho počiatočného stavu.

Verbosity nastavené na 2 vypíše základné štatistiky o experimente.
