This repository contains the software accompanying the paper 
"A formal proof of Ramsey(4,5)=24". 

## Install

The following installation instructions are for the Ubuntu OS.

### Install dependencies: polyml + HOL
This takes about 15 min to complete. The first following command is optional.
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
Please edit the config file: 
- choose and appropriate number of cores (default is 40)
- memory per core in megabyte (default is 8000)

The creation of a HOL4 proof is divided in multiple steps: 
enumeration, generalization, ...


### Enumeration
Enumeration of all the ramsey 4,4 graphs (R(4,4,k)) 
and all ramsey 3,5 graphs (R(3,5,k)) up to isomorphism:
```
load "enum"; open sat aiLib graph enum;
disable_log := true;
enum (4,4);
enum (3,5);
```
The results are stored in the directory ``enum``.

### Generalization
A generalization is set of edge and non-edge common to multiple graphs.
In practice, the generalization only need to cover 
one element of the isomorphism of each graph. (see picture in the paper)
Generalization are useful as they allow us to solve multiple cases simultaneously.
For each set R(3,5,k) (resp. (R(4,4,k)), we consturct a set of generalizion
G(3,5,k) (resp. (G(4,4,k)) with the following code.

```
load "enum"; open sat aiLib graph enum;
disable_log := true;
enum (4,4);
enum (3,5);
```

The results are stored in the directory ``gen``.
 
 
 
 
 
