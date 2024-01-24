This repository contains the software accompanying the paper 
"A formal proof of Ramsey(4,5)=24". 

## Install

The following installation instructions are for the Ubuntu OS.

### Install dependencies: polyml + HOL
This takes about 15 min to complete. The first following comman is optional.
``` 
sudo apt install -y libgmp-dev rlwrap
sh install_dep.sh
```

### Install ramsey
```
cd src
sh install.sh
```

After updating the repository (git pull), the command `sh install.sh` needs to be run again.

## Verifying the proof in HOL4 (wip)

The creation of a HOL4 proof is divided in multiple steps.

