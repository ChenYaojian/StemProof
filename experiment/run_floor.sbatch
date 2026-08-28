#!/bin/bash
#SBATCH -p debug
#SBATCH -J tnco_floor
#SBATCH -c 8
#SBATCH --mem=16G
#SBATCH -t 04:00:00
#SBATCH -o floor_%j.out
#SBATCH -e floor_%j.err
cd /home/cyj/cyj/TNC/floor_exp_2026
/home/cyj/anaconda3/envs/szq_tnc/bin/python grid_floor_experiment.py 6,8,10,12,16,20,24,28,32,36,40,44,48,53 128 8
