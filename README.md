This repository contains the software accompanying the paper 
"A formal proof of Ramsey(4,5)=24". 

### Install dependencies: polyml + HOL4
The following installation instructions are for the Ubuntu OS.
This takes about 15 min to complete. The first command is optional.
``` 
sudo apt install -y libgmp-dev rlwrap
sh install_dep.sh
```
The HOL4 scripts are found in subdirectories of the `src` directory.

### Install ramsey
Compute dependencies between SML files: `sh install.sh`
If one updates the repository (`git pull`), 
the command `sh install.sh` needs to be run again.

### Running HOL4 in an interactive session
- Start: `sh hol.sh`
- Exit: `ctrl + D`

### Configuration
Please edit the `src/config` file: 
- choose and appropriate number of cores
  (default is 40), 
  typically half of the number given by `lscpu` but
  also depending on the available RAM.
- memory per core in megabyte 
  (default is 8000, need to be increased to 20000 when gluing 3512s)


### Enumeration of generalizations (skip)
In the `src` directory, please download and extract 
the covers from `http://grid01.ciirc.cvut.cz/~thibault/gen.tar.gz`.
If you want to create your own covers, please follow the instruction
of the next paragraph otherwise skip to the paragraph "Definition".
Some randomness is introduced when sampling graphs, therefore
you will not get the same covers as in `gen.tar.gz` but it should
be of similar quality.

### Enumeration of generalizations (2 hours)
First, we enumerate of all the ramsey 4,4 graphs (R(4,4,k)) 
and all ramsey 3,5 graphs (R(3,5,k)) up to isomorphism.

Execute in an interactive session:
```
load "enum"; open sat aiLib graph enum;
disable_log := true;
enum (4,4);
enum (3,5);
```
The results are stored in the directory `enum`.
They can be read using the function `enum.read_enum`.

For each set R(3,5,k) (resp. (R(4,4,k)), we consturct a set of 
graph generalizations G(3,5,k) (resp. (G(4,4,k)) with the following code.

Execute in an interactive session:
```
load "gen"; open sat aiLib kernel graph gen;
select_basic := true;
erase_file (selfdir ^ "/gen/gen4418");
erase_file (selfdir ^ "/gen/gen3514");
select_number1 := 313;
select_number2 := 1;
val (_,t35) = add_time (gen (3,5)) (5,13);
select_number1 := 1000;
select_number2 := 100;
val (_,t44) = add_time (gen (4,4)) (4,17);
```

The results are stored in the directory `gen`. 
They can be read using the function `gen.read_cover`.

Better covers are uses for k=8,10,12, to generate those covers.
Because this will erase the `gen` directory,
First, save the previous computation with `mv gen gen_default`.
then run:

```
load "glue"; open glue;
(* a better cover for 3,5,8 and 4,4,16 cover *)
better_cover "better" (8,0,4,0.5); 
(* a better cover for 3,5,10 and 4,4,14 cover *)
better_cover "better" (10,4,4,0.5); 
(* a better cover for 3,5,12 and 4,4,12 cover *)
better_cover "better" (12,8,0,0.5); 
```

Then combine the produced `gen_`directory by overwriting the 
files on the `gen_default` directory with the files from the `gen_better` 
directories

### Definition (8 min)
Defines first-order representations of clique conditions and 
covers. The relatively long time is due to the size of the covers.
```
cd def
../../HOL/bin/Holmake 
```

### Degree constraints and final step of the proof (15 min)
Prove the degree constraints and that together with the
existence of a R(4,5,24)-graph, we would obtain the final theorem:
```
cd ../basicRamsey
../../HOL/bin/Holmake 
```

### Proof of the existence of a R(4,5,24)-graph (10 min)
This uses the graph taken from the file `r4524exist/r4524`:
```
cd ../r4524exist
../../HOL/bin/Holmake 
```

### Proof of the enumeration of generalizations (2 hour)
Create proof scripts for the 4,4,k enumeration lemmas
in an interactive session (The easier 3,5,k cases are proven within the final enumeration script):
```
load "enump"; open kernel enump;
val _ = range (8, 18, fn size => write_enumscripts 50 size (4,4));
```

Run the scripts (requires 500GB of ram for 40 cores) 
preferably inside a screen `screen -S enum`:
```
cd enump
../../HOL/bin/Holmake -j 40 | tee ../aaa_log_enump
```

Clean some created temporary files:
```
find /tmp -maxdepth 1 -type f -name 'MLTEMP*' ! -exec rm {} \;
```

First, create the final enumeration script in an interactive session:
```
load "enump"; open enump;
write_enumfinalscript ();
```

And then, run the script:
```
cd enumf
../../HOL/bin/Holmake
```

### Gluing 
The gluing steps involve calling the SAT solvers on problems encoding
the possibility of extending the coloring of two graphs G,H with |G| to a R(4,5,25) by coloring tranverse edges. 

#### Technicalities
Before starting a HOL4 session (`sh hol.sh` in the `src` directory) 
that will run the gluing we recommend creating
a screen `screen -S glue` and redirecting the output of
minisat if your temporary directory sits on a small partition
as such `export TMPDIR="$PWD/tmp"; mkdir tmp;`

Some temporary files (one per problem) may accumulate in the `/tmp` directory.
Please clean them regularly or at least at the end of each run.
```
cd /tmp
watch -n 600 "find . -maxdepth 1 -type f -name 'MLTEMP*' ! -exec rm {} \;"
```

We do not use `Holmake` for
this step as we do not know if it is possible to limit the amount of memory
it each core uses when calling its parallel version.

Therefore after a gluing case is done, it will be necessary to generate the dependencies for each theory file `/home/path/fooTheory` by running:
```
../../HOL/bin/genscriptdep /home/path/fooTheory.sig > /home/path/fooTheory.ui
../../HOL/bin/genscriptdep /home/path/fooTheory.sml > /home/path/fooTheory.uo
echo "/home/path/fooTheory" >> /home/path/fooTheory.ui
echo "/home/path/fooTheory.sig" >> /home/path/fooTheory.ui
echo "/home/path/fooTheory" >> /home/path/fooTheory.uo
echo "/home/path/fooTheory.sml" >> /home/path/fooTheory.uo
```

#### Gluing 3,5,8 (20 min, 20GB per core)
Change the memory limit in the `config` to 20GB.
Create the list of problems (`read_par` looks in the `gen` directory):
```
load "glue"; open aiLib kernel graph enum gen glue;
val ml1 = read_par 8 (3,5);
val ml2 = read_par 16 (4,4);
val pbl = shuffle (cartesian_product ml1 ml2);
write_pbl "glue358_pbl" pbl;
```

Create and run the scripts:
```
load "glue"; open aiLib kernel graph enum gen glue;
val glue358_pbl = read_pbl (selfdir ^ "/glue358_pbl");
run_script_pbl (selfdir ^ "/work_glue358") glue358_pbl;
```

#### Gluing 3,5,10 (18 days, 8GB per core)
Change the memory limit in the `config` to 8GB.
Create the list of problems:
```
load "glue"; open aiLib kernel graph enum gen glue;
val ml1 = read_par 10 (3,5);
val ml2 = read_par 14 (4,4);
val pbl = shuffle (cartesian_product ml1 ml2);
write_pbl "glue3510_pbl" pbl;
```

Create and run the scripts:
```
load "glue"; open aiLib kernel graph enum gen glue;
val glue3510_pbl = read_pbl (selfdir ^ "/glue3510_pbl");
run_script_pbl (selfdir ^ "/work_glue3510") glue3510_pbl;
```

#### Gluing 3,5,12 (16 days, 20GB per core)
Change the memory limit in the `config` to 20GB.
Create the list of problems:
```
load "glue"; open aiLib kernel graph enum gen glue;
val ml1 = read_par 12 (3,5);
val ml2 = read_par 12 (4,4);
val pbl = shuffle (cartesian_product ml1 ml2);
write_pbl "glue3512_pbl" pbl;
```

Create and run the scripts:
```
load "glue"; open aiLib kernel graph enum gen glue;
val glue3512_pbl = read_pbl (selfdir ^ "/glue3512_pbl");
run_script_pbl (selfdir ^ "/work_glue3512") glue3512_pbl;
```

Warning: we needed to restart the proof as one of the process
ended with an out of memory error.
After determining which script was killed by looking at which `fooTheory.sml`
was missing, we changed the memory limit
to 100 GB (to be safe) in the config file and restarted the proof
as follows:

```
load "glue"; open aiLib kernel graph enum gen glue;
val filel = listDir (selfdir ^ "/work_glue3512");
val filel1 = filter (String.isSuffix "Theory.sml") filel;
val filel2 = map (fn s => fst (split_string "Theory" s)) filel1;
fun f s = 
  let val (s1,s2,s3) = triple_of_list (String.tokens (fn x => x = #"_") s) in
    (stinf s2, stinf s3)
  end;
val pbldone = enew (cpl_compare IntInf.compare IntInf.compare) (map f filel2);
val pbl = read_pbl (selfdir ^ "/glue3512_pbl"));
val pbltodo = filter (fn x => not (emem x pbldone)) pbl;
write_pbl "glue3512_pbl_todo" pbltodo;
run_script_pbl (selfdir ^ "/work_glue3512") pbltodo;
```

## Merge the gluing lemmas (4 hours)
First, we create some functions to prove that we can merge the gluing lemmas
to prove that all the cases being covered
```
cd merge
../../HOL/bin/Holmake
```

In the `merge` directory, generate the scripts by `rlwrap ../../HOL/bin/hol`:

```
load "merge"; open merge;
write_mergescript8 ();
write_mergescripts 10;
write_mergescripts 12;
```

Run the scripts:
```
cd merge358
../../HOL/bin/Holmake --no_prereqs
```

```
cd merge3510
../../HOL/bin/Holmake --no_prereqs -j 22 | tee ../aaa_log_merge3510
```

```
cd merge3512
../../HOL/bin/Holmake --no_prereqs -j 12 | tee ../aaa_log_merge3512
```

## Final step of a proof











