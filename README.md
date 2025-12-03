# Audioport IP Block – I2S Output Interface  
Digital Design | SystemVerilog RTL | VHDL | SystemC | UVM Verification

This repository contains the complete design and verification environment of the **Audioport IP Block**, a digital subsystem implementing an **I2S audio output interface**.  
The project was developed as part of the **Digital Techniques 3 (DT3)** coursework and includes RTL design, SystemC/TLM modeling, verification using UVM, and simulation automation using TCL.

---

## 🎯 Overview

The Audioport IP block handles audio data transfer over the **I2S protocol**, including:
- Serial audio data transmission  
- Word select generation  
- Clock-domain crossings (CDC)  
- Control unit logic  
- DSP unit operations  
- Interrupt output  

The design follows a **mixed-language methodology**:
- **SystemVerilog RTL**  
- **VHDL** (`i2s_unit.vhd`)  
- **SystemC** behavioral and TLM models  
- **UVM** testbench  
- **TCL** simulation scripts (Questasim/Mentor)

This project demonstrates complete SoC-style digital design and DV flow—from RTL to SystemC modeling to full UVM verification.

---

## 📁 Repository Structure (logical layout)

### RTL (SystemVerilog + VHDL)
Includes:
- `i2s_unit.vhd`
- `control_unit.sv`
- `dsp_unit.sv`
- `cdc_unit.sv`
- `irq_out_if.sv`
- APB interface modules

### SystemC Models
High-level and TLM models for:
- Audioport
- DSP unit
- CDC components
- TLM CPU + DAC stubs
- Scoreboard models

### UVM Verification
A full UVM environment including:
- Agents (APB, IRQ, I2S, Control Unit)
- Drivers, Monitors, Transactions
- Audioport environment & package
- Scoreboard and predictor
- Sequences (main, ISR, master)
- Testcases and test configurations
- Assertion modules (`*_svamod.sv`)

### Simulation Scripts
Automated simulation and waveform setup:
- `0_setup_*.tcl`
- `1_vsim_*`
- `3_vsim_*`
- `5_vsim_*`
- Constraints (`*.sdc`)
- Synthesis directive files

---

## 🧪 Verification Methodology

This project uses **UVM Class Library** for:
- Constrained-random stimulus generation  
- Interface-based agents  
- Transaction-level communication  
- Scoreboarding & functional checking  
- Assertions for protocol correctness  
- Coverage-driven verification  

Both RTL and mixed-language simulations were executed using:
- **Questasim / Modelsim**
- **SystemC 2.3**  
- **TLM 2.0**

Gate-level (post-layout) simulations were also supported (cfg_gatelevel).

---

## 📡 I2S Interface Summary  
The I2S unit implements:
- BCLK generation  
- LRCLK / WS generation  
- Serial data shifting  
- Channel synchronization  
- Reset / enable control (from the Control Unit)  

It interacts with:
- DSP output data  
- Control unit timing  
- CDC synchronization modules  
- IRQ mechanism  
- APB register interface  

---

## 🛠 Tools Used  
- **SystemVerilog / VHDL RTL**  
- **SystemC / C++ (TLM)**  
- **UVM 1.2**  
- **Mentor Questasim / Modelsim**  
- **TCL automation**  
- **Synthesis scripts (.sdc)**  

---

## 📄 Notes  
This repository contains coursework material and does not include any proprietary or confidential design. All files are educational.

---

## 📬 Contact  
If you’d like to know more about the implementation or discuss digital design / verification topics, feel free to reach out.



Although the raw project folder is uploaded as-is, the logical structure of the design is:

