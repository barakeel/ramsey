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
- choose and appropriate number of cores, 
  typically half of the number given by `lscpu` but this also depends your 
  available RAM (default is 40).
- memory per core in megabyte (default is 8000)
- maximum number of holes in a generalization (default is 10)
  Decreasing this number to 8 will require less memory and RAM 
  at the cost of being slower.

The creation of a HOL4 proof is divided in multiple steps: 
enumeration, cone, glueing proof, definition, enumeration proof, cone proof.

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
load "cone"; open kernel cone;
val _ = range (11,17, fn i => if i = 13 then () else cones45 i (4,4));
```

The results are stored in the directory `cone`. 

### Glueing (4 days)

The first step is to generate proof scripts:
Execute in HOL:
```
load "glue"; open kernel glue;
fun f i = if i = 13 then () else
  write_gluescripts "glue" 50 true (4,4,i) (3,5,24-i) (4,5);
val _ = range (11,17,f);
```

Warning (before running the `glue.sh` bash script): 
The config file does not affect the following step.
The execution requires a total maximum of 300GB of RAM and 300GB of hard disk 
storage when run on 20 cores with `maxhole 10`. 
If you have more RAM and more hard disk storage 
you may increase the number of cores.

Run from the `src` directory (preferably inside a screen `screen -S glue`):
```
cd glue
cp ../def/Holmakefile Holmakefile
export TMPDIR="$PWD/tmp"
mkdir tmp
../../HOL/bin/Holmake -j 20 | tee ../aaa_log_glue
```

To be run at most one hour after starting the previous process,
remove empty temporary files (preferably inside a screen `screen -S tmp`).
This is unsafe if you have another process using files named `/tmp/MLTEMP*`.
```
cd /tmp
watch -n 600 "find . -maxdepth 1 -type f -name 'MLTEMP*' ! -exec lsof {} \; -exec rm {} \;"
```

Track the progress by running from the `src` directory: 
`ls glue/*Theory.sml | wc -l`.

When the process finishes, kill the `watch` process and remove the 
remaining temporary files `rm /tmp/MLTEMP*`

Look at a theorem:
```
load "glue/ramseyGlue_4414_3510_140Theory";
val sl = map fst (DB.thms "ramseyGlue_4414_3510_140");
val thm = DB.fetch "ramseyGlue_4414_3510_140" "RamseyGlue_4414_3510_9635";
```

### Definition (10 min)
```
cd def
../../HOL/bin/Holmake 
cd ..
```

Look at definitions:
```
load "def/ramseyDefTheory";
val sl = map fst (DB.definitions "ramseyDef");
val thm1 = DB.fetch "ramseyDef" "C4416r_DEF";
val thm2 = DB.fetch "ramseyDef" "G3512_DEF";
```

### Proving the enumeration (1 hour)
First, create some empty files by running `sh hol.sh`;

```
load "aiLib";
aiLib.erase_file "gen/gen4418";
aiLib.erase_file "gen/gen3514";
```

First we create the proof scripts by running `sh hol.sh`:

```
load "enump"; open kernel enump;
val _ = range (8, 18, fn size => write_enumscripts 50 size (4,4));
```

Run the scripts (requires 300GB of ram)
preferably inside a screen `screen -S enump`:

```
cd enump
echo "INCLUDES = .. ../def" > Holmakefile
../../HOL/bin/Holmake --no_prereqs -j 40 | tee ../aaa_log_enump
cd ..
```

This creates low-level lemmas for the difficult case that need to combined.
The final proof of the enumeration of 3,5,k graphs and 4,4,k graphs
is obtained by running:

Create the final enumeration script by running `sh hol.sh`:

```
load "enump"; open enump;
write_enumfinalscript ();
```

Then, run the script:
```
cd enumf
../../HOL/bin/Holmake --no_prereqs
cd ..
```

Look at a theorem:
```
load "enumf/ramseyEnumTheory";
val sl = map fst (DB.thms "ramseyEnum");
show_assums := true;
val thm = DB.fetch "ramseyEnum" "R4417";
```

### Proving the cone clauses (5 hours)

Write the scripts:
```
load "cone"; open kernel cone;
fun f i = if i = 13 then () else write_conescripts 10 i (4,4);
val _ = range (11,17,f);
```

Run the scripts (requires 300GB of ram)
preferably inside a screen `screen -S conep`:
```
cd conep
echo "INCLUDES = .. ../def" > Holmakefile
../../HOL/bin/Holmake --no_prereqs -j 40 | tee ../aaa_log_conep
cd ..
```

Look at a theorem:
```
load "conep/ramseyCone4412_0Theory";
val sl = map fst (DB.thms "ramseyCone4412_0");
show_assums := true;
val thm = DB.fetch "ramseyCone4412_0" "Cone4412_0";
```




 
