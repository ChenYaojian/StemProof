#!/bin/bash
#SBATCH -p debug
#SBATCH -J tnco_sens
#SBATCH -c 8
#SBATCH --mem=16G
#SBATCH -t 08:00:00
#SBATCH -o sens_%j.out
#SBATCH -e sens_%j.err
cd "$SLURM_SUBMIT_DIR"  # anonymized; original ran from the experiment directory
# Submitted as five parallel debug jobs, one line each (jobs 181893-181897):
python sensitivity_budget.py grid 28,32,36,44,53 512 8 results_sens_grid512.json
# python sensitivity_budget.py grid 36 4096 8 results_sens_grid4096_36.json
# python sensitivity_budget.py grid 53 4096 8 results_sens_grid4096_53.json
# python sensitivity_budget.py chip 2d_6x6_c16,2d_7x7_c8,2d_7x7_c12 512 8 results_sens_chip512.json
# python sensitivity_budget.py chip 2d_6x6_c16,2d_7x7_c12 4096 8 results_sens_chip4096.json
