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


### Enumeration (10 min)
Enumeration of all the ramsey 4,4 graphs (R(4,4,k)) 
and all ramsey 3,5 graphs (R(3,5,k)) up to isomorphism:

```
sh hol.sh
```

```
load "enum"; open sat aiLib graph enum;
disable_log := true;
enum (4,4);
enum (3,5);
```

To exit, ``ctrl + D``.
The results are stored in the directory ``enum``.
They can be read using the function ``enum.read_enum``.

### Generalization (2 hours)
A generalization is set of edge and non-edge common to multiple graphs.
In practice, the generalization only need to cover 
one element of the isomorphism of each graph. (see picture in the paper)
Generalization are useful as they allow us to solve multiple cases simultaneously.
For each set R(3,5,k) (resp. (R(4,4,k)), we consturct a set of generalizion
G(3,5,k) (resp. (G(4,4,k)) with the following code.

```
sh hol.sh
```

```
load "gen"; open sat aiLib kernel graph gen;
select_number1 := 313;
select_number2 := 1;
val (_,t35) = add_time (gen (3,5)) (5,13);
select_number1 := 1000;
select_number2 := 100;
val (_,t44) = add_time (gen (4,4)) (4,17);
```

To exit, ``ctrl + D``.
The results are stored in the directory ``gen``. 
They can be read using the function ``gen.read_cover``.

### Definition (10 min)
One can create definitions for the generalizations and their relation with
the set of clauses C(a,b,k) defining R(a,b,k)

```
cd def
../../HOL/bin/Holmake
cd ..
```

You can check the definitions by running in HOL ``sh hol.sh``:

```
load "def/ramseyDefTheory";
val sl = map fst (DB.definitions "ramseyDef");
val thm1 = DB.fetch "ramseyDef" "C4416r_DEF";
val thm2 = DB.fetch "ramseyDef" "G3512_DEF";
```

### Cone




### Glueing 
The next three steps are independent






 
