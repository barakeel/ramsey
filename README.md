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

From now on, the scripts are found and run in the `src` directory.

``` 
cd src
```

### Install ramsey
Compute dependencies between SML files: `sh install.sh`
If one updates the repository (`git pull`), 
the command `sh install.sh` needs to be run again.

### Running HOL4
- Start: `sh hol.sh`
- Exit: `ctrl + D`

## Verifying the proof in HOL4
Please edit the config file: 
- choose and appropriate number of cores (default is 40)
- memory per core in megabyte (default is 8000)

The creation of a HOL4 proof is divided in multiple steps: 
enumeration/generalization, cones, glueing, definitions, enumeration/
generalization proof, cone proof, 
a special case and many gathering steps.

### Enumeration (10 min)
Enumeration of all the ramsey 4,4 graphs (R(4,4,k)) 
and all ramsey 3,5 graphs (R(3,5,k)) up to isomorphism.

Execute in HOL:
```
load "enum"; open sat aiLib graph enum;
disable_log := true;
enum (4,4);
enum (3,5);
```

The results are stored in the directory `enum`.
They can be read using the function `enum.read_enum`.

### Generalization (2 hours)
A generalization is set of edge and non-edge common to multiple graphs.
In practice, the generalization only need to cover 
one element of the isomorphism of each graph. (see picture in the paper)
Generalization are useful as they allow us to solve multiple cases 
simultaneously. For each set R(3,5,k) (resp. (R(4,4,k)), we consturct a set of 
graph generalizations G(3,5,k) (resp. (G(4,4,k)) with the following code.

Execute in HOL:
```
load "gen"; open sat aiLib kernel graph gen;
select_number1 := 313;
select_number2 := 1;
val (_,t35) = add_time (gen (3,5)) (5,13);
select_number1 := 1000;
select_number2 := 100;
val (_,t44) = add_time (gen (4,4)) (4,17);
```

The results are stored in the directory `gen`. 
They can be read using the function `gen.read_cover`.

### Cone (2 hours)

This code create both the cones and the cone generalizations.

Execute in HOL:
```
load "gen"; load "sat"; load "cone";
open aiLib kernel graph sat nauty gen cone;
store_log := true;
val (_,tcone) = add_time 
 range (11,17, fn i => if i = 13 then () else cones45 i (4,4));
```

The results are stored in the directory `cone`. 

### Glueing (2 days)

The first step is to generate proof scripts (fast):
Execute in HOL:
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

Warning (before running the `glue.sh` bash script): 
The config file does not affect the following step.
The execution requires total maximum of 300GB when run on 18 cores (default).
Memory of the partition where the repository sits must be higher than 300GB.

Run from the `src` directory (preferably inside a screen `screen -S glue`):
```
cd glue
cp ../def/Holmakefile Holmakefile
export TMPDIR="$PWD/tmp"
mkdir tmp
../../HOL/bin/Holmake -j 18 | tee ../aaa_log_glue
```

To be run at most one hour after starting the previous process,
remove empty temporary files (preferably inside a screen `screen -S tmp`):
```
cd /tmp
watch -n 600 "find . -maxdepth 1 -type f -name 'MLTEMP*' ! -exec lsof {} \; -exec rm {} \;"
```

Track the progress by running from the `src` directory: 
`ls glue/*Theory.sml | wc -l`.

When the process finishes, kill the `watch` process and remove the 
remaining temporary files `rm /tmp/MLTEMP*`

### Definition (10 min)
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

### Proving the enumeration
The proof of the enumeration of 3,5,k1 graphs and 4,4,k2 graphs for small k2
is obtained by running:

```
cd enumi
../../HOL/bin/Holmake
cd ..
```

For bigger k2, the proof is parallelized









 
