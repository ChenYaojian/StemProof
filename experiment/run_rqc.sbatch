#!/bin/bash
#SBATCH -p debug
#SBATCH -J tnco_rqc
#SBATCH -c 8
#SBATCH --mem=16G
#SBATCH -t 04:00:00
#SBATCH -o rqc_%j.out
#SBATCH -e rqc_%j.err
cd "$SLURM_SUBMIT_DIR"  # anonymized; original ran from the experiment directory
python rqc_stem_experiment.py 128 8
