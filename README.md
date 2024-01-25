This repository contains the software accompanying the paper 
"A formal proof of Ramsey(4,5)=24". 

## Install

The following installation instructions are for the Ubuntu OS.

### Install dependencies: polyml + HOL4
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

### Cone (2 hours)

This code create both the cones and the cone generalizations.

```
load "gen"; load "sat"; load "cone";
open aiLib kernel graph sat nauty gen cone;
store_log := true;
val (_,tcone) = add_time 
 range (11,17, fn i => if i = 13 then () else cones45 i (4,4));
```

The results are stored in the directory ``cone``. 

### Glueing (A very long time)

The first step is to generate some proof scripts:

```
load "glue"; open aiLib kernel graph syntax sat gen glue;
val dirname = "glue";
write_gluescripts dirname 1 true (4,4,17) (3,5,7) (4,5);
write_gluescripts dirname 1 true (4,4,16) (3,5,8) (4,5);
write_gluescripts dirname 50 true (4,4,15) (3,5,9) (4,5);
write_gluescripts dirname 50 true (4,4,14) (3,5,10) (4,5);
write_gluescripts dirname 50 true (4,4,12) (3,5,12) (4,5);
write_gluescripts dirname 50 true (4,4,11) (3,5,13) (4,5);
```

The files in the directory ``glue`` are the generated proof scripts.
The glueing calls an external minisat on many problems and might take a very long time:
```
cd glue
cp ../def/Holmakefile Holmakefile
../../HOL/bin/Holmake -j 40 --maxheap=8000 | tee aaa_log_glue
```


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














 
