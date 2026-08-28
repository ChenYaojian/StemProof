#!/bin/bash
#SBATCH -p debug
#SBATCH -J tnco_rqc
#SBATCH -c 8
#SBATCH --mem=16G
#SBATCH -t 04:00:00
#SBATCH -o rqc_%j.out
#SBATCH -e rqc_%j.err
cd /home/cyj/cyj/TNC/floor_exp_2026
/home/cyj/anaconda3/envs/szq_tnc/bin/python rqc_stem_experiment.py 128 8
