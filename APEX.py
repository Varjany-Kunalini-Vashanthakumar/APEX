#!/usr/bin/env python3

"""
APEX - Action Potential Examination Platform
Advanced Cardiac Electrophysiology Analysis Suite

Copyright © 2025-2026, University of Bern, Institute of Physiology, Odening Lab
Authors: Varjany Kunalini Vashanthakumar (VkV), Katja E. Odening

This source code is licensed under the MIT License found in the
LICENSE file in the root directory of this source tree.

Developed with AI assistance.

For citation:
    Vashanthakumar VK, Odening KE. APEX: Action Potential Examination 
    Platform for cardiac electrophysiology analysis. (2026). 
    GitHub: https://github.com/varjany-kunalini-vashanthakumar/APEX
    DOI: 10.5281/zenodo.22994510

Development History:
================================================================================
APEX - Action Potential Examination Platform
Advanced Cardiac Electrophysiology Analysis Suite

FIXES (May 2026):
1. Fixed multiple corrections stacking - only one peak per AP
2. Fixed batch correction dialog with intelligent pre-selection
3. Fixed correction persistence with order independence
4. Multiple corrections can coexist (peak + upstroke + late repol)
5. Combined correction types shown in table
6. FIXED: Adaptive smoothing based on sampling rate and species
7. FIXED: Mouse AP detection with species-specific thresholds
8. FIXED: dV/dt_max validation with warnings
9. FIXED: Species-specific smoothing suggestions
10. FIXED: Mouse APD30/APD50 thresholds (as low as 2-5ms accepted)
11. FIXED: Cell grouping for stacking - same cell across frequencies grouped
12. FIXED: PatchMaster/HEKA CSV file support with proper metadata extraction
13. FIXED: Sync zoom with interactive selectors (preserves zoom state)
14. FIXED: dV/dt_max calculation with manual upstroke selection - strictly uses selected window
15. FIXED: Export raw vs corrected APD80/APD90 when late repolarization correction applied
16. FIXED: Cardioid AP detection with lower thresholds (APD30 min 5ms, APD50 min 10ms)
17. FIXED: Artifact rejection to properly find biological APs after stimulation
18. FIXED: Empty smoothing_ms value handling (TclError fix)
19. ENHANCED: dV/dt_max calculation with minimal smoothing on upstroke region only
20. ENHANCED: Dual-path analysis for accurate upstroke velocity with high global smoothing
21. ENHANCED: Upstroke quality validation with confidence scoring
22. FIXED: Smoothing disabled when smoothing window = 0
23. FIXED: Average trace figures x-axis starts at -50ms
24. ADDED: User settings persistence (save/load configuration)
25. ADDED: Incremental analysis (preserve results when adding new files)
26. FIXED: Stacked grouping analysis matches single trace analysis
27. ADDED: Named configuration save/load with file dialogs
28. ADDED: Reset analysis settings button
29. FIXED: Split Parameter_Averages into Raw, Corrected, and Combined sheets
30. REMOVED: Redundant Confirm Analysis button
31. ADDED: Filename sanitization for export (fixes OSError)
32. ADDED: Cardioid Immature Mode for early-stage cell detection
33. ADDED: Minimal smoothing trace for dV/dt_max accuracy with high global smoothing
34. ADDED: Console warnings for high smoothing usage

May 2026 UPDATE:
35. REMOVED: All AP rejection restrictions - every peak with a computable RMP and
    peak time is now accepted (unrestricted mode)
36. ADDED: Movable vertical cursor for upstroke-start selection

================================================================================
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import pandas as pd
import numpy as np
import os
from pathlib import Path
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.patches import ConnectionPatch, Rectangle, Ellipse
from matplotlib.gridspec import GridSpec
import matplotlib
matplotlib.use('TkAgg')
from scipy import signal
from scipy.ndimage import gaussian_filter1d
from scipy.signal import savgol_filter, find_peaks
import math
import datetime
import json
import traceback
import re
from collections import defaultdict, OrderedDict
import warnings
import seaborn as sns
from tkinter import simpledialog
import multiprocessing
from concurrent.futures import ThreadPoolExecutor
import hashlib
import zipfile
from reportlab.lib import colors
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, Image
from reportlab.lib.styles import getSampleStyleSheet

# Optional ABF support
try:
    import pyabf
    ABF_AVAILABLE = True
except ImportError:
    ABF_AVAILABLE = False
    print("pyabf not available. ABF file support disabled.")

# Optional for publication figures
try:
    from matplotlib import font_manager
    FONT_AVAILABLE = True
except ImportError:
    FONT_AVAILABLE = False

# Suppress warnings
warnings.filterwarnings('ignore', category=RuntimeWarning)
warnings.filterwarnings('ignore', category=UserWarning)

# ============================================================================
# APEX Configuration with Professional Enhancements
# ============================================================================
TIME_KEYS = ['time', 't', 'time(ms)', 'time_ms', 'time (ms)', 'timestamp', 'Time', 'Time (ms)']
VOLT_KEYS = ['voltage', 'v', 'v_mem', 'vm', 'vmon(mv)', 'v-mon(mv)', 'v_mon_mV', 'v (mV)', 'v_mV', 'v (mv)', 'membrane', 'voltage (mV)', 'Vmon', 'Vm', 'Voltage']

# Species-specific parameters with enhanced ranges and min_apd90
SPECIES_PARAMS = {
    'rabbit': {
        'default_y_range': (-90, 80),
        'expected_dvdt_max': (100, 300),
        'apd90_range': (150, 350),
        'apd30_range': (50, 120),
        'apd50_range': (80, 200),
        'rmp_range': (-90, -60),
        'plateau_threshold': 0.7,
        'min_peak_prominence': 15,
        'min_apd90': 50,
        'min_apd30': 20,
        'min_apd50': 40,
        'suggested_smoothing_ms': 0.8,
        'color': '#E41A1C',
        'marker': 'o'
    },
    'mouse': {
        'default_y_range': (-90, 60),
        'expected_dvdt_max': (200, 500),
        'apd90_range': (15, 80),
        'apd30_range': (2, 25),
        'apd50_range': (8, 45),
        'rmp_range': (-90, -60),
        'plateau_threshold': 0.6,
        'min_peak_prominence': 20,
        'min_apd90': 15,
        'min_apd30': 2,
        'min_apd50': 2,
        'suggested_smoothing_ms': 0.6,
        'color': '#377EB8',
        'marker': 's'
    },
    'zebrafish': {
        'default_y_range': (-90, 40),
        'expected_dvdt_max': (50, 150),
        'apd90_range': (100, 250),
        'apd30_range': (30, 80),
        'apd50_range': (50, 120),
        'rmp_range': (-90, -55),
        'plateau_threshold': 0.5,
        'min_peak_prominence': 10,
        'min_apd90': 60,
        'min_apd30': 20,
        'min_apd50': 30,
        'suggested_smoothing_ms': 2.5,
        'color': '#4DAF4A',
        'marker': '^'
    },
    'cardioid': {
        'default_y_range': (-80, 40),
        'expected_dvdt_max': (100, 450),
        'apd90_range': (50, 400),
        'apd30_range': (5, 60),
        'apd50_range': (10, 100),
        'rmp_range': (-90, -30),
        'plateau_threshold': 0.5,
        'min_peak_prominence': 10,
        'min_apd90': 50,
        'min_apd30': 5,
        'min_apd50': 10,
        'suggested_smoothing_ms': 0.8,
        'color': '#984EA3',
        'marker': 'D'
    },
    'default': {
        'default_y_range': (-90, 80),
        'expected_dvdt_max': (50, 300),
        'apd90_range': (50, 400),
        'apd30_range': (20, 150),
        'apd50_range': (30, 220),
        'rmp_range': (-85, -60),
        'plateau_threshold': 0.6,
        'min_peak_prominence': 15,
        'min_apd90': 30,
        'min_apd30': 10,
        'min_apd50': 15,
        'suggested_smoothing_ms': 1.5,
        'color': '#999999',
        'marker': 'v'
    }
}

# Publication color schemes
PUBLICATION_PALETTES = {
    'nature': ['#E64B35', '#4DBBD5', '#00A087', '#3C5488', '#F39B7F', '#8491B4', '#91D1C2', '#DC0000', '#7E6148', '#B09C85'],
    'science': ['#1F78B4', '#33A02C', '#E31A1C', '#FF7F00', '#6A3D9A', '#B15928', '#A6CEE3', '#B2DF8A', '#FB9A99', '#FDBF6F'],
    'cell': ['#3182BD', '#E6550D', '#31A354', '#756BB1', '#636363', '#BD9E39', '#AD494A', '#8C6D31', '#843C39', '#7B4173']
}

# Enhanced APD percentages for restitution curves (INCLUDES APD95)
APD_PERCENTAGES = [10, 20, 30, 40, 50, 60, 70, 80, 90, 95]
FREQUENCIES = ['0.5', '1.0', '2.0', '3.0', '4.0', '5.0']

# Frequency to x-axis limit mapping (ms)
FREQUENCY_XLIMITS = {
    '0.5': 2000,
    '1.0': 1000,
    '2.0': 500,
    '3.0': 350,
    '4.0': 250,
    '5.0': 200
}

# Common drugs for pharmacological experiments
COMMON_DRUGS = [
    'None', 'Control', 'Vehicle',
    'E-4031', 'dofetilide', 'HMR-1556','d-sotalol', 'quinidine',
    'nifedipine', 'verapamil', 'diltiazem',
    'isoproterenol', 'propranolol', 'atenolol',
    '4-AP', 'TEA', 'chromanol 293B',
    'ouabain', 'digoxin',
    'ranolazine', 'lidocaine', 'flecainide',
    'TTX', 'ATX-II',
    'Other'
]

# Default configuration for settings persistence
DEFAULT_CONFIG = {
    'selected_species': 'auto',
    'yaxis_auto': True,
    'yaxis_min': -90.0,
    'yaxis_max': 80.0,
    'smoothing': True,
    'smoothing_ms': '',
    'smooth_method': 'savgol',
    'use_corrected_apd': True,
    'use_dual_path_detection': True,
    'filter_outliers': True,
    'visual_filter_only': True,
    'sync_zoom': False,
    'output_folder': '',
    'cardioid_immature_mode': False,  # CHANGE 2: New config option
    'export_settings': {
        'ap_parameter_matrix': True,
        'raw_ap_data': True,
        'frequency_drug_response': True,
        'comprehensive_analysis': True,
        'individual_traces': True,
        'average_traces': True,
        'ap_overlay_raw': False,
        'average_ap_sem': False,
        'drug_comparison': False,
        'frequency_comparison': False,
        'stv_analysis': True,
        'normalized_ap': False,
        'one_figure_per_cell': False
    }
}

# CHANGE 1: Filename sanitization helper function
def sanitize_filename(filename, max_length=200):
    """
    Sanitize filename by removing/replacing invalid characters.
    Prevents OSError when creating files with newlines or special characters.
    
    Args:
        filename: Original filename string
        max_length: Maximum allowed filename length
    
    Returns:
        Sanitized filename safe for file system
    """
    if not filename:
        return "unnamed"
    
    # Convert to string if not already
    filename = str(filename)
    
    # Replace newlines and carriage returns
    filename = filename.replace('\n', '_').replace('\r', '_')
    
    # Replace Windows invalid characters
    invalid_chars = '<>:"/\\|?*'
    for char in invalid_chars:
        filename = filename.replace(char, '_')
    
    # Replace parentheses and brackets
    filename = filename.replace('(', '_').replace(')', '_')
    filename = filename.replace('[', '_').replace(']', '_')
    
    # Replace spaces and tabs with underscores
    filename = filename.replace(' ', '_').replace('\t', '_')
    
    # Remove multiple consecutive underscores
    filename = re.sub(r'_+', '_', filename)
    
    # Strip leading/trailing underscores and spaces
    filename = filename.strip('_').strip()
    
    # Ensure non-empty
    if not filename:
        filename = "unnamed"
    
    # Truncate if too long
    if len(filename) > max_length:
        filename = filename[:max_length]
    
    # Remove any remaining non-ASCII characters
    filename = re.sub(r'[^\x00-\x7F]+', '_', filename)
    
    return filename


def sanitize_excel_sheet_name(sheet_name, max_length=31):
    """
    Sanitize Excel sheet name according to Excel limitations.
    Excel sheet names:
    - Max 31 characters
    - Cannot contain: [ ] : * ? / \
    - Cannot start or end with '
    
    Args:
        sheet_name: Original sheet name
        max_length: Maximum length (Excel limit is 31)
    
    Returns:
        Sanitized sheet name safe for Excel
    """
    if not sheet_name:
        return "Sheet1"
    
    sheet_name = str(sheet_name)
    
    # Replace invalid Excel characters
    invalid_chars = '[]:*?/\\'
    for char in invalid_chars:
        sheet_name = sheet_name.replace(char, '_')
    
    # Replace newlines
    sheet_name = sheet_name.replace('\n', '_').replace('\r', '_')
    
    # Remove multiple underscores
    sheet_name = re.sub(r'_+', '_', sheet_name)
    
    # Trim to max length
    if len(sheet_name) > max_length:
        sheet_name = sheet_name[:max_length]
    
    # Remove leading/trailing apostrophes
    sheet_name = sheet_name.strip("'")
    
    # Ensure non-empty
    if not sheet_name:
        sheet_name = "Sheet1"
    
    return sheet_name


def get_config_path():
    """Get path to configuration file"""
    return os.path.join(os.path.expanduser("~"), ".apex_config.json")

def save_config(config_data):
    """Save configuration to file"""
    try:
        config_path = get_config_path()
        with open(config_path, 'w') as f:
            json.dump(config_data, f, indent=2)
        return True
    except Exception as e:
        print(f"Error saving config: {e}")
        return False

def load_config():
    """Load configuration from file"""
    try:
        config_path = get_config_path()
        if os.path.exists(config_path):
            with open(config_path, 'r') as f:
                config = json.load(f)
                # Merge with defaults for any missing keys
                for key, value in DEFAULT_CONFIG.items():
                    if key not in config:
                        config[key] = value
                return config
    except Exception as e:
        print(f"Error loading config: {e}")
    return DEFAULT_CONFIG.copy()

# ============================================================================
# ENHANCED: Dual-Path dV/dt_max Calculation Functions
# ============================================================================

def calculate_dvdt_with_minimal_smoothing(voltage, time, onset_idx, peak_idx, dt_ms, species='default', minimal_smoothing_ms=0):
    """
    Calculate dV/dt_max using MINIMAL smoothing ONLY on the upstroke region.
    This ensures accurate upstroke velocity regardless of global smoothing settings.
    
    Args:
        voltage: Full voltage trace
        time: Full time trace
        onset_idx: Index of upstroke onset
        peak_idx: Index of AP peak
        dt_ms: Time step in milliseconds
        species: Species for validation
        minimal_smoothing_ms: Fixed minimal smoothing window (default 0 ms)
    
    Returns:
        tuple: (dvdt_max, dvdt_max_idx, warnings_list)
    """
    warnings_list = []
    
    # Validate inputs
    if onset_idx >= peak_idx or onset_idx < 0 or peak_idx >= len(voltage):
        warnings_list.append("Invalid onset/peak indices for dV/dt calculation")
        return np.nan, None, warnings_list
    
    # Extract ONLY the upstroke region
    upstroke_voltage = voltage[onset_idx:peak_idx + 1]
    upstroke_time = time[onset_idx:peak_idx + 1]
    
    if len(upstroke_voltage) < 3:
        # Fallback: simple difference
        dvdt_max = (voltage[peak_idx] - voltage[onset_idx]) / (time[peak_idx] - time[onset_idx])
        warnings_list.append(f"Upstroke region too short ({len(upstroke_voltage)} points), using simple subtraction")
        return dvdt_max, onset_idx, warnings_list
    
    # Apply MINIMAL smoothing for derivative calculation
    # This preserves the true upstroke velocity while reducing noise
    minimal_window_samples = max(3, int(round(minimal_smoothing_ms / dt_ms)))
    if minimal_window_samples % 2 == 0:
        minimal_window_samples += 1
    
    # Clamp to valid range
    upstroke_len = len(upstroke_voltage)
    if minimal_window_samples > upstroke_len:
        minimal_window_samples = upstroke_len if upstroke_len % 2 == 1 else upstroke_len - 1
    if minimal_window_samples < 3:
        minimal_window_samples = 3
    
    try:
        # Use Savitzky-Golay filter for derivative with minimal smoothing
        dvdt = savgol_filter(
            upstroke_voltage,
            window_length=minimal_window_samples,
            polyorder=min(3, minimal_window_samples - 1),
            deriv=1,
            delta=dt_ms
        )
        
        if len(dvdt) > 0:
            dvdt_max = np.max(dvdt)
            dvdt_max_idx_in_upstroke = np.argmax(dvdt)
            dvdt_max_idx = onset_idx + dvdt_max_idx_in_upstroke
        else:
            dvdt_max = (voltage[peak_idx] - voltage[onset_idx]) / (time[peak_idx] - time[onset_idx])
            dvdt_max_idx = onset_idx
            warnings_list.append("Empty derivative array, using simple subtraction")
    
    except Exception as e:
        # Fallback to simple derivative calculation
        dvdt = np.gradient(upstroke_voltage, dt_ms)
        if len(dvdt) > 0:
            dvdt_max = np.max(dvdt)
            dvdt_max_idx_in_upstroke = np.argmax(dvdt)
            dvdt_max_idx = onset_idx + dvdt_max_idx_in_upstroke
        else:
            dvdt_max = (voltage[peak_idx] - voltage[onset_idx]) / (time[peak_idx] - time[onset_idx])
            dvdt_max_idx = onset_idx
        warnings_list.append(f"Savitzky-Golay derivative failed: {str(e)[:50]}")
    
    # Validate against species expectations
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    min_expected, max_expected = species_params.get('expected_dvdt_max', (50, 300))
    
    if not np.isnan(dvdt_max):
        if dvdt_max < min_expected * 0.5:
            warnings_list.append(f"dV/dt_max ({dvdt_max:.1f}) seems low for {species}")
        elif dvdt_max > max_expected * 1.5:
            warnings_list.append(f"dV/dt_max ({dvdt_max:.1f}) seems high for {species}")
    
    return dvdt_max, dvdt_max_idx, warnings_list


def validate_upstroke_quality(voltage, time, onset_idx, peak_idx, dt_ms):
    """
    Calculate confidence score for dV/dt_max measurement.
    
    Args:
        voltage: Voltage trace
        time: Time trace
        onset_idx: Upstroke onset index
        peak_idx: Peak index
        dt_ms: Time step in milliseconds
    
    Returns:
        dict: Quality metrics including confidence score (0-1)
    """
    upstroke_voltage = voltage[onset_idx:peak_idx + 1]
    upstroke_time = time[onset_idx:peak_idx + 1]
    
    n_samples = len(upstroke_voltage)
    
    # Calculate signal-to-noise ratio in upstroke region
    # Use first 5 points of upstroke as baseline for noise estimation
    baseline_samples = min(5, n_samples // 4 if n_samples > 10 else n_samples)
    if baseline_samples > 0:
        noise_estimate = np.std(upstroke_voltage[:baseline_samples])
        signal_amplitude = np.max(upstroke_voltage) - np.min(upstroke_voltage)
        snr = signal_amplitude / (noise_estimate + 1e-10)
    else:
        snr = 1
    
    # Calculate slope consistency (should be smooth, not jagged)
    if n_samples >= 5:
        dvdt = np.gradient(upstroke_voltage, dt_ms)
        if len(dvdt) > 0:
            # Coefficient of variation of derivative (lower = more consistent)
            dvdt_cv = np.std(dvdt) / (np.mean(np.abs(dvdt)) + 1e-10)
            slope_consistency = max(0, 1 - min(1, dvdt_cv / 2))
        else:
            slope_consistency = 0.5
    else:
        slope_consistency = 0.3
    
    # Score based on number of samples (more samples = better)
    expected_samples = 20  # Typical number for good upstroke
    sample_score = min(1.0, n_samples / expected_samples)
    
    # Score based on SNR
    target_snr = 20  # Desired SNR
    snr_score = min(1.0, snr / target_snr)
    
    # Combined confidence score (weighted average)
    confidence_score = (sample_score * 0.3 + snr_score * 0.4 + slope_consistency * 0.3)
    confidence_score = max(0.0, min(1.0, confidence_score))
    
    # Determine quality level
    if confidence_score >= 0.8:
        quality = "Excellent"
    elif confidence_score >= 0.6:
        quality = "Good"
    elif confidence_score >= 0.4:
        quality = "Fair"
    else:
        quality = "Poor"
    
    return {
        'confidence_score': confidence_score,
        'quality': quality,
        'n_samples': n_samples,
        'snr': snr,
        'slope_consistency': slope_consistency,
        'sample_score': sample_score,
        'snr_score': snr_score
    }


def compare_dvdt_calculations(voltage, time, onset_idx, peak_idx, dt_ms, global_smoothing_ms, species='default'):
    """
    Compare dV/dt_max calculated with global smoothing vs minimal upstroke smoothing.
    For diagnostic purposes only - prints to console.
    
    Args:
        voltage: Full voltage trace
        time: Full time trace
        onset_idx: Upstroke onset index
        peak_idx: AP peak index
        dt_ms: Time step in milliseconds
        global_smoothing_ms: Global smoothing window used
        species: Species for validation
    
    Returns:
        tuple: (dvdt_global, dvdt_minimal, diff_percent)
    """
    # Method 1: Global smoothing derivative (original method)
    upstroke_voltage_global = voltage[onset_idx:peak_idx + 1]
    
    if len(upstroke_voltage_global) >= 3:
        global_window_samples = max(3, int(round(global_smoothing_ms / dt_ms)))
        if global_window_samples % 2 == 0:
            global_window_samples += 1
        global_window_samples = min(global_window_samples, len(upstroke_voltage_global) - 1 if len(upstroke_voltage_global) % 2 == 0 else len(upstroke_voltage_global))
        
        if global_window_samples >= 3:
            try:
                dvdt_global_arr = savgol_filter(
                    upstroke_voltage_global,
                    window_length=global_window_samples,
                    polyorder=min(3, global_window_samples - 1),
                    deriv=1,
                    delta=dt_ms
                )
                dvdt_global = np.max(dvdt_global_arr) if len(dvdt_global_arr) > 0 else np.nan
            except:
                dvdt_global = np.nan
        else:
            dvdt_global = np.nan
    else:
        dvdt_global = np.nan
    
    # Method 2: Minimal smoothing upstroke-only (new method)
    dvdt_minimal, _, _ = calculate_dvdt_with_minimal_smoothing(voltage, time, onset_idx, peak_idx, dt_ms, species)
    
    # Calculate percent difference
    if not np.isnan(dvdt_global) and not np.isnan(dvdt_minimal) and dvdt_global > 0:
        diff_percent = ((dvdt_minimal - dvdt_global) / dvdt_global) * 100
    else:
        diff_percent = np.nan
    
    # Print comparison to console (for verification only)
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    expected_min, expected_max = species_params.get('expected_dvdt_max', (50, 300))
    
    print(f"\n[APEX dV/dt Comparison]")
    print(f"  Species: {species}")
    print(f"  Global smoothing: {global_smoothing_ms:.2f} ms")
    print(f"  dV/dt (global):    {dvdt_global:.1f} mV/ms" if not np.isnan(dvdt_global) else "  dV/dt (global):    N/A")
    print(f"  dV/dt (upstroke minimal): {dvdt_minimal:.1f} mV/ms" if not np.isnan(dvdt_minimal) else "  dV/dt (upstroke minimal): N/A")
    if not np.isnan(diff_percent):
        print(f"  Difference: {diff_percent:+.1f}%")
    print(f"  Expected range for {species}: {expected_min}-{expected_max} mV/ms")
    
    # Add warning if global smoothing excessively blunts the upstroke
    if not np.isnan(dvdt_global) and not np.isnan(dvdt_minimal) and dvdt_global > 0:
        if diff_percent > 30:  # Global smoothing is reducing dV/dt by more than 30%
            print(f"  ⚠️ WARNING: Global smoothing ({global_smoothing_ms:.1f}ms) significantly blunts dV/dt!")
            print(f"     Using upstroke-minimal method which reports {dvdt_minimal:.1f} mV/ms vs {dvdt_global:.1f} mV/ms")
    print()
    
    return dvdt_global, dvdt_minimal, diff_percent


# ============================================================================
# NEW: Adaptive Smoothing Functions
# ============================================================================

def calculate_adaptive_smoothing(dt_ms, species='default', file_type='CSV'):
    """
    Calculate optimal smoothing window based on sampling rate and species
    
    Args:
        dt_ms: Time step in milliseconds
        species: 'rabbit', 'mouse', 'zebrafish', 'cardioid', 'default'
        file_type: 'ABF' or 'CSV/Excel'
    
    Returns:
        optimal_smoothing_ms: Recommended smoothing window in ms
    """
    sampling_rate_hz = 1000.0 / dt_ms if dt_ms > 0 else 1000
    
    # Get species-specific base smoothing
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    base_smoothing = species_params.get('suggested_smoothing_ms', 1.5)
    
    # Adjust based on file type and sampling rate
    if file_type == 'ABF':
        # ABF files typically have high sampling rate (>10kHz)
        if sampling_rate_hz > 20000:
            smoothing_factor = 0.4
        elif sampling_rate_hz > 10000:
            smoothing_factor = 0.6
        elif sampling_rate_hz > 5000:
            smoothing_factor = 0.8
        else:
            smoothing_factor = 1.0
    else:
        # CSV/Excel files from PatchMaster may have variable sampling rates
        # For HEKA/PatchMaster data, typical rates are 10-50 kHz
        if sampling_rate_hz > 20000:
            smoothing_factor = 0.5
        elif sampling_rate_hz > 10000:
            smoothing_factor = 0.7
        elif sampling_rate_hz > 5000:
            smoothing_factor = 1.0
        elif sampling_rate_hz > 2000:
            smoothing_factor = 1.3
        elif sampling_rate_hz > 1000:
            smoothing_factor = 1.6
        else:
            smoothing_factor = 2.0  # Low sampling rate needs more smoothing
    
    optimal = base_smoothing * smoothing_factor
    
    # Clamp to reasonable range
    optimal = max(0.3, min(5.0, optimal))
    
    return optimal


def validate_dvdt_max(dvdt_max, species, smoothing_ms, sampling_rate_hz):
    """
    Validate dV/dt_max and return warnings if problematic
    
    Args:
        dvdt_max: Calculated dV/dt_max value
        species: Species name
        smoothing_ms: Smoothing window used (ms)
        sampling_rate_hz: Sampling rate in Hz
    
    Returns:
        list of warning strings
    """
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    min_val, max_val = species_params.get('expected_dvdt_max', (50, 300))
    
    warnings = []
    
    if dvdt_max is None or np.isnan(dvdt_max):
        warnings.append("dV/dt_max could not be calculated")
        return warnings
    
    if dvdt_max < min_val:
        warnings.append(f"dV/dt_max ({dvdt_max:.1f}) BELOW expected range ({min_val}-{max_val} mV/ms)")
        if smoothing_ms > 1.5:
            warnings.append(f"  → Try reducing smoothing from {smoothing_ms:.1f}ms to 0.5-1.0ms for {species}")
        if sampling_rate_hz < 2000:
            warnings.append(f"  → Low sampling rate ({sampling_rate_hz:.0f}Hz) may limit accuracy")
    elif dvdt_max > max_val:
        warnings.append(f"dV/dt_max ({dvdt_max:.1f}) ABOVE expected range ({min_val}-{max_val} mV/ms)")
        if smoothing_ms < 1.0:
            warnings.append(f"  → Try increasing smoothing from {smoothing_ms:.1f}ms to 2-3ms for {species}")
        if sampling_rate_hz > 20000:
            warnings.append(f"  → Very high sampling rate ({sampling_rate_hz:.0f}Hz) may amplify noise")
    else:
        warnings.append(f"dV/dt_max ({dvdt_max:.1f}) within expected range ({min_val}-{max_val} mV/ms)")
    
    # Check sampling rate adequacy
    if sampling_rate_hz < 1000:
        warnings.append(f"⚠️ Sampling rate ({sampling_rate_hz:.0f}Hz) is low - may affect AP shape accuracy")
    
    return warnings


def get_species_min_apd90(species):
    """Get species-specific minimum APD90 for validation"""
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    return species_params.get('min_apd90', 30)


def get_species_smoothing_suggestion(species):
    """Get suggested smoothing for a species"""
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    return species_params.get('suggested_smoothing_ms', 1.5)


# ============================================================================
# CHANGE 2: Enhanced Cardioid AP Validation with Immature Mode
# ============================================================================

def is_cardioid_ap(ap_metrics, species='cardioid', immature_mode=False):
    """
    Cardioid validation is also unrestricted in this build.
    """
    rmp = ap_metrics.get('RMP', np.nan)
    peak_v = ap_metrics.get('peak_time', np.nan)

    if rmp is None or math.isnan(rmp):
        return False, "RMP could not be determined"
    if peak_v is None or math.isnan(peak_v):
        return False, "Peak could not be determined"

    return True, "Valid Cardioid AP (unrestricted mode)"


def is_physiologically_valid_ap(ap_metrics, species='default', min_apa=20, immature_mode=False):
    """
    APEX accepts every trace that has a measurable RMP and a peak.
    All species-specific thresholds are disabled; the function only
    checks that the two essential quantities exist.
    """
    rmp = ap_metrics.get('RMP', np.nan)
    peak_v = ap_metrics.get('peak_time', np.nan)

    if rmp is None or math.isnan(rmp):
        return False, "RMP could not be determined"
    if peak_v is None or math.isnan(peak_v):
        return False, "Peak could not be determined"

    # Everything else is accepted — no APA / APD / dV/dt thresholds.
    return True, "Valid AP (unrestricted mode)"


def find_automatic_upstroke_start(time, voltage, peak_idx, rmp, dt_ms):
    """
    Find upstroke start at the intersection of RMP horizontal line and upstroke rise.
    """
    dvdt = np.gradient(voltage, dt_ms)
    
    upstroke_start_search = max(0, peak_idx - int(100 / dt_ms))
    upstroke_region = slice(upstroke_start_search, peak_idx)
    
    if np.any(dvdt[upstroke_region] > 0):
        max_dvdt_region = np.max(dvdt[upstroke_region])
        threshold = max_dvdt_region * 0.1
        
        for i in range(upstroke_start_search, peak_idx):
            if dvdt[i] > threshold:
                rise_start_idx = i
                
                for j in range(rise_start_idx, upstroke_start_search - 1, -1):
                    if voltage[j] <= rmp:
                        if voltage[j] >= rmp - 0.5:
                            start_idx = j
                            return start_idx, time[start_idx], voltage[start_idx]
                        else:
                            for k in range(j, rise_start_idx):
                                if voltage[k] >= rmp:
                                    return k, time[k], voltage[k]
                
                for k in range(upstroke_start_search, rise_start_idx):
                    if voltage[k] >= rmp:
                        return k, time[k], voltage[k]
                
                return rise_start_idx, time[rise_start_idx], voltage[rise_start_idx]
    
    for i in range(peak_idx, upstroke_start_search - 1, -1):
        if voltage[i] >= rmp:
            return i, time[i], voltage[i]
    
    start_idx = max(0, peak_idx - int(20 / dt_ms))
    return start_idx, time[start_idx], voltage[start_idx]


def compute_corrected_apd_from_fit_v2(time, voltage, peak_idx, rmp, peak_v):
    """
    Calculate corrected APD80/90 using linear fit between APD50, APD60, and APD70.
    """
    apa = peak_v - rmp
    
    apd50_time = find_crossing_time(time, voltage, peak_idx, rmp + 0.5 * apa)
    apd60_time = find_crossing_time(time, voltage, peak_idx, rmp + 0.4 * apa)
    apd70_time = find_crossing_time(time, voltage, peak_idx, rmp + 0.3 * apa)
    
    fit_times = []
    fit_voltages = []
    
    if apd50_time:
        fit_times.append(apd50_time)
        fit_voltages.append(rmp + 0.5 * apa)
    if apd60_time:
        fit_times.append(apd60_time)
        fit_voltages.append(rmp + 0.4 * apa)
    if apd70_time:
        fit_times.append(apd70_time)
        fit_voltages.append(rmp + 0.3 * apa)
    
    if len(fit_times) >= 2:
        coef = np.polyfit(fit_times, fit_voltages, 1)
        slope, intercept = coef
        
        v80 = rmp + 0.2 * apa
        v90 = rmp + 0.1 * apa
        
        apd80_corrected = (v80 - intercept) / slope - time[peak_idx]
        apd90_corrected = (v90 - intercept) / slope - time[peak_idx]
        
        apd80_corrected = max(apd80_corrected, 0)
        apd90_corrected = max(apd90_corrected, 0)
        
        fit_range = (min(fit_times), max(fit_times))
        
        return apd80_corrected, apd90_corrected, slope, intercept, fit_range
    
    return None, None, None, None, None


def find_crossing_time(time, voltage, start_idx, target_voltage):
    """Find time when voltage crosses target level after peak"""
    for i in range(start_idx, len(time) - 1):
        if voltage[i] <= target_voltage:
            t0, v0 = time[i - 1], voltage[i - 1]
            t1, v1 = time[i], voltage[i]
            if v1 != v0:
                frac = (target_voltage - v0) / (v1 - v0)
                return t0 + frac * (t1 - t0)
    return None


def find_crossing_time_upstroke(time, voltage, start_idx, target_voltage):
    """Find time when voltage crosses target level (for upstroke detection)"""
    for i in range(start_idx, len(time) - 1):
        if voltage[i] >= target_voltage:
            t0, v0 = time[i - 1], voltage[i - 1]
            t1, v1 = time[i], voltage[i]
            if v1 != v0:
                frac = (target_voltage - v0) / (v1 - v0)
                return t0 + frac * (t1 - t0)
    return None


def calculate_dvdt_from_points(voltage, time, start_idx, peak_idx, dt, is_manual_selection=False):
    """Calculate dV/dt from user-selected start to detected peak
    
    Args:
        voltage: voltage trace
        time: time trace
        start_idx: start index (upstroke start)
        peak_idx: peak index
        dt: time step in ms
        is_manual_selection: if True, strictly use only points between start_idx and peak_idx
    """
    if start_idx >= peak_idx or start_idx < 0 or peak_idx >= len(voltage):
        return np.nan, None
    
    # When manual selection is used, strictly confine to the selected window
    if is_manual_selection:
        # Use exactly the points between start_idx and peak_idx
        upstroke_voltage = voltage[start_idx:peak_idx + 1]
        upstroke_time = time[start_idx:peak_idx + 1]
        
        if len(upstroke_voltage) < 3:
            dvdt_max = (voltage[peak_idx] - voltage[start_idx]) / (time[peak_idx] - time[start_idx])
            return dvdt_max, start_idx
        
        try:
            # Use minimal window for manual selections to preserve true slope
            window_length = min(5, len(upstroke_voltage) - 1 if len(upstroke_voltage) % 2 == 0 else len(upstroke_voltage))
            if window_length < 3:
                window_length = 3
            
            dvdt = savgol_filter(upstroke_voltage,
                                 window_length=window_length,
                                 polyorder=min(3, window_length - 1),
                                 deriv=1,
                                 delta=dt)
            dvdt_max = np.max(dvdt)
            dvdt_max_idx_in_upstroke = np.argmax(dvdt)
            dvdt_max_idx = start_idx + dvdt_max_idx_in_upstroke
            return dvdt_max, dvdt_max_idx
        except Exception as e:
            print(f"Savitzky-Golay derivative failed for manual selection: {e}")
            dvdt_max = (voltage[peak_idx] - voltage[start_idx]) / (time[peak_idx] - time[start_idx])
            return dvdt_max, start_idx
    else:
        # Original behavior for automatic detection
        upstroke_voltage = voltage[start_idx:peak_idx + 1]
        upstroke_time = time[start_idx:peak_idx + 1]
        
        if len(upstroke_voltage) >= 3:
            try:
                window_length = min(11, len(upstroke_voltage) - 1 if len(upstroke_voltage) % 2 == 0 else len(upstroke_voltage))
                if window_length < 3:
                    window_length = 3
                
                dvdt = savgol_filter(upstroke_voltage,
                                     window_length=window_length,
                                     polyorder=min(3, window_length - 1),
                                     deriv=1,
                                     delta=dt)
                dvdt_max = np.max(dvdt)
                dvdt_max_idx_in_upstroke = np.argmax(dvdt)
                dvdt_max_idx = start_idx + dvdt_max_idx_in_upstroke
                return dvdt_max, dvdt_max_idx
            except Exception as e:
                print(f"Savitzky-Golay derivative failed: {e}")
                dvdt_max = (voltage[peak_idx] - voltage[start_idx]) / (time[peak_idx] - time[start_idx])
                return dvdt_max, start_idx
        else:
            dvdt_max = (voltage[peak_idx] - voltage[start_idx]) / (time[peak_idx] - time[start_idx])
            return dvdt_max, start_idx


def extract_ap_window(voltage, peak_idx, dt_ms, window_before=50, window_after=150):
    """Extract window around AP for shape comparison"""
    if peak_idx is None or peak_idx < 0 or peak_idx >= len(voltage):
        return None
    
    samples_before = int(window_before / dt_ms) if dt_ms > 0 else 50
    samples_after = int(window_after / dt_ms) if dt_ms > 0 else 150
    
    start = max(0, peak_idx - samples_before)
    end = min(len(voltage), peak_idx + samples_after)
    
    if end - start < 10:
        return None
    
    return voltage[start:end]


def find_similar_aps_by_morphology(current_ap_metrics, all_results, current_trace_idx,
                                   current_ap_idx, threshold=0.85, dt_ms=0.1):
    """
    Find APs with similar morphology based on:
    - APA (action potential amplitude)
    - APD50 (mid-repolarization)
    - dV/dt_max (upstroke velocity)
    - RMP
    - AP shape correlation
    """
    similar_aps = []
    
    current_features = {
        'apa': current_ap_metrics.get('APA', 0),
        'apd50': current_ap_metrics.get('APD50', 0),
        'dvdt_max': current_ap_metrics.get('dVdt_max', 0),
        'rmp': current_ap_metrics.get('RMP', 0),
        'peak_time': current_ap_metrics.get('peak_time', 0)
    }
    
    if current_trace_idx < len(all_results):
        current_trace = all_results[current_trace_idx]
        current_peak_idx = current_ap_metrics.get('peak_idx', 0)
        current_window = extract_ap_window(current_trace['voltage_smooth'],
                                           current_peak_idx, dt_ms)
    else:
        current_window = None
    
    for trace_idx, trace in enumerate(all_results):
        for ap_idx, ap in enumerate(trace.get('ap_metrics', [])):
            if trace_idx == current_trace_idx and ap_idx == current_ap_idx:
                continue
            
            similarity = calculate_similarity_score(current_ap_metrics, ap)
            
            if similarity >= threshold:
                similar_aps.append((trace_idx, ap_idx, similarity))
    
    return sorted(similar_aps, key=lambda x: x[2], reverse=True)


def validate_apd_values(apd90, species='default'):
    """Validate APD90 is physiologically possible"""
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    expected_min, expected_max = species_params['apd90_range']
    
    if apd90 is None or np.isnan(apd90):
        return False, None
    
    if apd90 < 5:
        return False, "APD90 too short (<5 ms)"
    
    if apd90 > expected_max * 3:
        return False, f"APD90 too long (> {expected_max * 3:.0f} ms)"
    
    if apd90 < expected_min * 0.5:
        return False, f"APD90 suspiciously short (< {expected_min * 0.5:.0f} ms)"
    
    return True, None


# ============================================================================
# Enhanced APD Metrics with Per-Trace RMP and Automatic Upstroke Detection
# ============================================================================

def compute_apd_metrics_enhanced_v3(time, voltage, peak_idx, stim_times_idx=None,
                                    species='default', use_corrected_apd=True,
                                    manual_upstroke_idx=None, immature_mode=False):
    """Enhanced AP metrics calculation with per-trace RMP detection"""
    if peak_idx <= 0 or peak_idx >= len(voltage) - 1:
        raise ValueError("Peak index out of range")
    
    dt = time[1] - time[0] if len(time) > 1 else 0.1
    
    rmp, rmp_method = calculate_rmp_from_baseline(time, voltage, baseline_window_ms=10)
    
    peak_v = float(voltage[peak_idx])
    apa = peak_v - rmp
    overshoot = peak_v - 0.0
    
    if apa < 10:
        apa_warning = f"APA ({apa:.1f} mV) is unusually low"
    else:
        apa_warning = None
    
    # Get global smoothing value for diagnostic comparison
    global_smoothing_ms = 1.5  # Default, will be updated later if available
    
    if manual_upstroke_idx is not None:
        # Use strict upstroke window for manual selections to avoid stimulation artifact
        dvdt_max, dvdt_max_idx = calculate_dvdt_from_points(voltage, time, manual_upstroke_idx, peak_idx, dt, is_manual_selection=True)
        onset_idx = manual_upstroke_idx
        # Validate that the calculated dV/dt_max is physiologically plausible
        if species == 'cardioid' and immature_mode:
            expected_min, expected_max = 5, 600  # Very wide range for immature cardioid
        else:
            expected_min, expected_max = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])['expected_dvdt_max']
        is_physiological = expected_min <= dvdt_max <= expected_max if not np.isnan(dvdt_max) else False
        quality_metrics = None  # Initialize quality_metrics to None for manual upstroke
        dvdt_warnings = []  # Initialize empty warnings list
    else:
        onset_idx, onset_time, onset_voltage = find_automatic_upstroke_start(time, voltage, peak_idx, rmp, dt)
        
        # Use ENHANCED dV/dt calculation with minimal smoothing on upstroke region
        dvdt_max, dvdt_max_idx, dvdt_warnings = calculate_dvdt_with_minimal_smoothing(
            voltage, time, onset_idx, peak_idx, dt, species
        )
        
        # For diagnostic purposes: compare with global smoothing method
        # This is hidden from the user but prints to console for verification
        try:
            compare_dvdt_calculations(voltage, time, onset_idx, peak_idx, dt, global_smoothing_ms, species)
        except:
            pass  # Silent fail for diagnostic function
        
        if species == 'cardioid' and immature_mode:
            expected_min, expected_max = 5, 600  # Very wide range for immature cardioid
        else:
            expected_min, expected_max = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])['expected_dvdt_max']
        is_physiological = expected_min <= dvdt_max <= expected_max if not np.isnan(dvdt_max) else False
        
        # Store upstroke quality metrics
        quality_metrics = validate_upstroke_quality(voltage, time, onset_idx, peak_idx, dt)
    
    def apd_percent(percent):
        level = rmp + (1 - percent / 100.0) * apa
        for i in range(peak_idx, len(voltage) - 1):
            if voltage[i] <= level:
                t0, v0 = time[i - 1], voltage[i - 1]
                t1, v1 = time[i], voltage[i]
                if v1 == v0:
                    return time[i] - time[peak_idx]
                frac = (level - v0) / (v1 - v0)
                t_cross = t0 + frac * (t1 - t0)
                return float(t_cross - time[peak_idx])
        return np.nan
    
    apd_metrics = {}
    for percent in APD_PERCENTAGES:
        apd_metrics[f'APD{percent}'] = apd_percent(percent)
    
    apd90 = apd_metrics.get('APD90', np.nan)
    apd90_valid, apd90_warning = validate_apd_values(apd90, species)
    
    if not apd90_valid:
        apd_metrics['APD90_warning'] = apd90_warning
        apd50 = apd_metrics.get('APD50', np.nan)
        if not np.isnan(apd50) and apd50 > 0:
            estimated_apd90 = apd50 * 1.5
            apd_metrics['APD90_estimated'] = estimated_apd90
    
    apd50 = apd_metrics.get('APD50', np.nan)
    apd90 = apd_metrics.get('APD90', np.nan)
    
    # ========== ADD THIS NEW SECTION HERE ==========
    # For cardioid immature mode, be much more permissive with APD
    # The user's manual peak selection is correct
    if species == 'cardioid' and immature_mode:
        # CRITICAL: If we got here via manual peak selection, be very permissive
        if manual_upstroke_idx is not None:
            # This is a manually selected peak - be very permissive
            min_apd90 = 10
            min_apd30 = 2
            min_apd50 = 5
        else:
            min_apd90 = 25
            min_apd30 = 5
            min_apd50 = 10
    else:
        species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
        min_apd90 = species_params.get('min_apd90', 30)
        min_apd30 = species_params.get('min_apd30', 10)
        min_apd50 = species_params.get('min_apd50', 15)
    # ========== END OF NEW SECTION ==========
    
    if not math.isnan(apd50) and not math.isnan(apd90) and apd90 > 0:
        repolarization_fraction = (apd90 - apd50) / apd90
    else:
        repolarization_fraction = np.nan
    
    apd_metrics['Repolarization_Fraction'] = repolarization_fraction
    apd_metrics['has_bump'] = False
    apd_metrics['use_corrected_apd'] = use_corrected_apd
    
    result = {
        'RMP': rmp,
        'RMP_method': rmp_method,
        'APA': apa,
        'APA_warning': apa_warning,
        'Overshoot': overshoot,
        'dVdt_max': dvdt_max,
        'dVdt_max_physiological': is_physiological,
        'peak_time': float(time[peak_idx]),
        'peak_idx': int(peak_idx),
        'onset_idx': int(onset_idx) if onset_idx is not None else np.nan,
        'dvdt_max_idx': int(dvdt_max_idx) if not math.isnan(dvdt_max_idx) else np.nan,
        'species': species,
        'upstroke_manual': manual_upstroke_idx is not None,
        'has_manual_correction': False,
        'has_manual_upstroke': manual_upstroke_idx is not None,
        'has_late_repol': False,
        'correction_type': 'auto',
        'previous_peak_idx': peak_idx,
        'late_repolarization_corrected': False
    }
    
    # Add upstroke quality metrics if available
    if quality_metrics is not None:
        result['upstroke_quality_score'] = quality_metrics['confidence_score']
        result['upstroke_quality'] = quality_metrics['quality']
        result['upstroke_n_samples'] = quality_metrics['n_samples']
        result['upstroke_snr'] = quality_metrics['snr']
    
    # Add dvdt warnings if any
    if dvdt_warnings:
        result['dvdt_warnings'] = '; '.join(dvdt_warnings[:3])  # Limit to first 3 warnings
    
    result.update(apd_metrics)
    
    if not is_physiological and not np.isnan(dvdt_max):
        if species == 'cardioid' and immature_mode:
            expected_min, expected_max = 5, 600
        else:
            expected_min, expected_max = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])['expected_dvdt_max']
        result['dvdt_warning'] = f"dV/dt_max ({dvdt_max:.1f} mV/ms) outside expected range for {species} ({expected_min}-{expected_max} mV/ms)"
    
    return result


def apply_late_repolarization_correction_to_metrics(time, voltage, ap_metrics, peak_idx, rmp, peak_v):
    """Apply late repolarization correction to existing AP metrics using APD50-APD70 fit"""
    corrected_apd80, corrected_apd90, slope, intercept, fit_range = compute_corrected_apd_from_fit_v2(
        time, voltage, peak_idx, rmp, peak_v
    )
    
    if corrected_apd80 is not None and corrected_apd90 is not None:
        ap_metrics['APD80_raw'] = ap_metrics.get('APD80', np.nan)
        ap_metrics['APD90_raw'] = ap_metrics.get('APD90', np.nan)
        ap_metrics['APD80'] = corrected_apd80
        ap_metrics['APD90'] = corrected_apd90
        ap_metrics['has_bump'] = True
        ap_metrics['late_repolarization_corrected'] = True
        ap_metrics['has_late_repol'] = True
        
        if ap_metrics.get('correction_type', 'auto') == 'auto':
            ap_metrics['correction_type'] = 'late_repol'
        elif 'late_repol' not in ap_metrics['correction_type']:
            ap_metrics['correction_type'] += '+late_repol'
        
        ap_metrics['bump_fit_slope'] = slope
        ap_metrics['bump_fit_intercept'] = intercept
        ap_metrics['bump_fit_range'] = fit_range
        
        apd50 = ap_metrics.get('APD50', np.nan)
        if not math.isnan(apd50) and corrected_apd90 > 0:
            ap_metrics['Repolarization_Fraction'] = (corrected_apd90 - apd50) / corrected_apd90
        
        return True
    return False


# ============================================================================
# CHANGE 3: Enhanced Trace Analysis with Minimal Smoothing Trace
# ============================================================================

def analyze_trace_enhanced_dualpath_v3(time, voltage, species='default', smoothing=True,
                                       smooth_method='savgol', smoothing_ms=None,
                                       min_apd90=50.0, use_biological_peak_detection=False,
                                       use_corrected_apd=True, file_type='CSV',
                                       immature_mode=False):
    """
    Enhanced trace analysis with dual-path peak detection and physiological validation
    FIXED: Adaptive smoothing based on sampling rate and species
    CHANGE 1: Disable adaptive smoothing when smoothing window is set to 0
    CHANGE 3: Create minimally-smoothed trace for accurate upstroke detection
    """
    if len(time) < 10 or len(voltage) < 10:
        return {
            'time': np.array(time),
            'voltage_raw': np.array(voltage),
            'voltage_smooth': np.array(voltage),
            'voltage_minimal_smooth': np.array(voltage),
            'dt_ms': 0.1,
            'detection': {'stim_times_idx': np.array([]), 'stim_times_ms': [],
                          'real_ap_peaks_idx': np.array([]), 'raw_peaks': np.array([]),
                          'smooth_peaks': np.array([])},
            'ap_metrics': [],
            'stv_apd90': np.nan,
            'stv_note': 'Insufficient data',
            'adaptive_smoothing_used': None
        }
    
    dt_ms = float(time[1] - time[0]) if len(time) > 1 else 0.1
    sampling_rate_hz = 1000.0 / dt_ms if dt_ms > 0 else 1000
    
    # CHANGE 3: Create minimally-smoothed trace for accurate upstroke detection
    # This preserves dV/dt_max accuracy regardless of user's smoothing setting
    minimal_smoothing_ms = 0  # Fixed minimal smoothing
    
    # Check if smoothing is disabled
    smoothing_disabled = (not smoothing) or (smoothing_ms is not None and smoothing_ms <= 0)
    
    if smoothing_disabled:
        # NO SMOOTHING of any kind
        v_smooth = voltage.copy()
        v_lightly_filtered = voltage.copy()
        adaptive_smoothing_used = False
        smoothing_ms_used = 0
        light_smoothing_ms = 0
        # Still create minimal smooth trace (with minimal smoothing for derivative)
        v_minimal_smooth = smooth_voltage(voltage, method='savgol', 
                                          window_ms=minimal_smoothing_ms, dt_ms=dt_ms) if dt_ms > 0 else voltage
    else:
        # Smoothing is enabled
        if smoothing_ms is None or smoothing_ms <= 0:
            smoothing_ms = calculate_adaptive_smoothing(dt_ms, species, file_type)
            adaptive_smoothing_used = True
            smoothing_ms_used = smoothing_ms
        else:
            adaptive_smoothing_used = False
            smoothing_ms_used = smoothing_ms
        
        v_lightly_filtered = voltage.copy()
        if dt_ms > 0 and len(voltage) > 10:
            light_smoothing_ms = max(0.5, smoothing_ms_used * 0.1)
            v_lightly_filtered = smooth_voltage(voltage, method='gaussian',
                                                window_ms=light_smoothing_ms, dt_ms=dt_ms)
        
        v_smooth = smooth_voltage(voltage, method=smooth_method, window_ms=smoothing_ms_used, dt_ms=dt_ms) if smoothing else voltage
        
        # CHANGE 3: Create minimally-smoothed trace for accurate upstroke detection
        # Use fixed minimal smoothing regardless of user's setting
        
        # Create minimally-smoothed trace for accurate upstroke detection
        minimal_smoothing_ms = 0
        v_minimal_smooth = smooth_voltage(voltage, method='savgol',
                                          window_ms=minimal_smoothing_ms, dt_ms=dt_ms) if dt_ms > 0 else voltage
        
        # CHANGE 4: Add console warning when high smoothing is used
        if smoothing_ms_used > 3.0:
            print(f"\n[APEX Smoothing Notice]")
            print(f"  High smoothing ({smoothing_ms_used:.1f} ms) may affect AP shape.")
            print(f"  dV/dt_max is calculated using minimal smoothing ({minimal_smoothing_ms:.1f} ms) for accuracy.")
            print()
    
    # Use minimally-smoothed trace for upstroke detection and dV/dt calculation
    detection = distinguish_stimulation_vs_ap(time, v_lightly_filtered, dt_ms, min_apd90_ms=min_apd90,
                                            use_biological_peak_detection=use_biological_peak_detection,
                                            species=species, immature_mode=immature_mode)
    
    final_peaks, raw_peaks, smooth_peaks = dual_path_peak_detection(
        time, v_lightly_filtered, v_smooth, dt_ms, species
    )
    
    detection['real_ap_peaks_idx'] = final_peaks
    detection['raw_peaks'] = raw_peaks
    detection['smooth_peaks'] = smooth_peaks
    
    ap_metrics = []
    for p in final_peaks:
        try:
            m = compute_apd_metrics_enhanced_v3(time, v_minimal_smooth, p, detection.get('stim_times_idx', []),
                                                species, use_corrected_apd, immature_mode=immature_mode)
            ap_metrics.append(m)
        except Exception as e:
            print(f"Error computing enhanced metrics for peak {p}: {e}")
            continue
    
    valid_ap_metrics = []
    for m in ap_metrics:
        if species == 'cardioid':
            is_valid, reason = is_cardioid_ap(m, species, immature_mode)
        else:
            is_valid, reason = is_physiologically_valid_ap(m, species, min_apa=20)
        if is_valid:
            valid_ap_metrics.append(m)
        else:
            print(f"Rejected AP at peak time {m.get('peak_time', 'unknown')}: {reason}")
    
    ap_metrics = valid_ap_metrics
    
    apd90_values = [m.get('APD90', np.nan) for m in ap_metrics if not math.isnan(m.get('APD90', np.nan))]
    stv_apd90, stv_note = calculate_stv(apd90_values)
    
    result = {
        'time': np.array(time),
        'voltage_raw': np.array(voltage),
        'voltage_smooth': np.array(v_smooth),
        'voltage_minimal_smooth': np.array(v_minimal_smooth),
        'dt_ms': dt_ms,
        'detection': detection,
        'ap_metrics': ap_metrics,
        'stv_apd90': stv_apd90,
        'stv_note': stv_note,
        'dual_path_used': True,
        'use_corrected_apd': use_corrected_apd,
        'adaptive_smoothing_used': adaptive_smoothing_used if not smoothing_disabled else False,
        'smoothing_ms_used': smoothing_ms_used,
        'sampling_rate_hz': sampling_rate_hz,
        'immature_mode_used': immature_mode
    }
    
    return result


# ============================================================================
# About APEX Dialog (ENHANCED with tabs for documentation)
# ============================================================================

class AboutAPEXDialog(tk.Toplevel):
    """About dialog for APEX Platform with smoothing documentation"""
    
    def __init__(self, parent):
        super().__init__(parent)
        self.parent = parent
        
        self.title("About APEX Platform")
        self.geometry("750x650")
        self.transient(parent)
        self.grab_set()
        
        self.configure(bg='white')
        
        notebook = ttk.Notebook(self)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Tab 1: About APEX
        about_frame = ttk.Frame(notebook)
        notebook.add(about_frame, text="About APEX")
        
        header = ttk.Label(about_frame, text="APEX Platform",
                           font=("Helvetica", 16, "bold"), background='white')
        header.pack(pady=10)
        
        subtitle = ttk.Label(about_frame, text="Action Potential Examination Platform",
                             font=("Helvetica", 12), background='white')
        subtitle.pack()
        
        version = ttk.Label(about_frame, text="Professional Cardiac Electrophysiology Analysis Suite",
                            font=("Helvetica", 10), background='white')
        version.pack(pady=5)
        
        ttk.Separator(about_frame, orient='horizontal').pack(fill=tk.X, padx=20, pady=10)
        
        copyright_text = ttk.Label(about_frame,
                                   text=""" Copyright © 2025, University of Bern, Institute of Physiology
            Varjany Kunalini Vashanthakumar (VkV), developed in Odening lab \n
            Developed with AI Assistance""",
                                   font=("Helvetica", 10), background='white', justify=tk.CENTER)
        copyright_text.pack(pady=10)
        
        features_frame = ttk.LabelFrame(about_frame, text="Key Features", padding=10)
        features_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        features_text = """
• Per-trace RMP measurement from baseline (no automatic correction)
• Adaptive smoothing based on sampling rate and species
• Species-specific AP detection (mouse, rabbit, zebrafish, cardioid)
• dV/dt_max validation with intelligent warnings
• ENHANCED: Dual-path dV/dt calculation with minimal upstroke smoothing
• ENHANCED: Upstroke quality validation with confidence scoring
• Dual-path peak detection (raw + smoothed)
• Automatic upstroke detection at RMP/upstroke intersection
• Interactive upstroke start selection for accurate dV/dt_max
• Enhanced late repolarization detection with APD50-APD70 linear fit
• SELECTIVE batch correction for similar AP morphologies
• Multiple corrections can coexist (peak + upstroke + late repol)
• Intelligent pre-selection of similar APs (>80% similarity)
• Progress feedback for batch operations
• Single active correction per AP for visual clarity
• Visible APD lines (APD10-95) on plots
• Repolarization fraction calculation
• Professional Excel stacking with frequency detection
• Correct STV calculation and Poincaré plots
• 10 publication-quality figure types
• Comprehensive metadata management
• Batch processing and validation system
• Professional export system with organized folders
• User settings persistence (saves your preferences)
• Incremental analysis (preserve results when adding new files)
• Named configuration save/load with file dialogs
• Reset analysis settings button
• Split Parameter_Averages into Raw, Corrected, and Combined sheets
• NEW: Cardioid Immature Mode for early-stage cell detection
• NEW: Filename sanitization prevents OSError on export
• NEW: dV/dt_max accuracy preserved with high smoothing (uses minimal smoothing trace)
• NEW: Unrestricted AP acceptance mode (no biological filtering)
• NEW: Movable vertical cursor for upstroke-start selection
"""
        features_label = ttk.Label(features_frame, text=features_text,
                                   font=("Courier", 9), justify=tk.LEFT)
        features_label.pack(fill=tk.BOTH, expand=True)
        
        # Tab 2: Smoothing Guide
        smoothing_frame = ttk.Frame(notebook)
        notebook.add(smoothing_frame, text="Smoothing Guide")
        
        smoothing_scroll = scrolledtext.ScrolledText(smoothing_frame, wrap=tk.WORD, font=("Courier", 10))
        smoothing_scroll.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        smoothing_guide_text = """
SMOOTHING GUIDE FOR APEX
========================

WHEN TO USE SMOOTHING
---------------------
• Use smoothing when your raw data has visible noise
• Set smoothing window = 0 to completely disable all smoothing
• Adaptive smoothing is automatically used when smoothing window is empty

RECOMMENDED SMOOTHING WINDOWS BY SPECIES
----------------------------------------
Species      | Recommended | Range
-------------|-------------|----------
Mouse        | 0.6 ms      | 0.5-1.0 ms
Rabbit       | 0.8 ms      | 0.5-1.5 ms
Zebrafish    | 2.5 ms      | 2.0-3.5 ms
Cardioid     | 0.8 ms      | 0.5-1.5 ms

EFFECT OF SMOOTHING ON dV/dt_max
-------------------------------
• Excessive smoothing (>3 ms) will ARTIFICIALLY REDUCE dV/dt_max
• APEX uses dual-path analysis: minimal smoothing (0.5ms) for upstroke only
• The reported dV/dt_max uses upstroke-minimal method for accuracy
• Global smoothing affects AP shape and APD measurements

WHY DISABLE SMOOTHING (Set window = 0)?
--------------------------------------
• Your data is already very clean (high SNR)
• You want to preserve every detail of the raw trace
• You're working with high-frequency components
• For publication requiring raw data display

WARNING SIGNS OF OVER-SMOOTHING
-------------------------------
• dV/dt_max is unusually low for your species
• Upstroke looks rounded or flattened
• Small features (notches, EADs) disappear
• APD values are systematically changed

WHAT SMOOTHING METHOD TO CHOOSE?
-------------------------------
Savitzky-Golay:
• Preserves signal features (peaks, notches)
• Better for quantitative analysis
• Default method for APEX

Gaussian:
• More aggressive smoothing
• Better for very noisy data
• May blur fine details

TROUBLESHOOTING
-------------
If dV/dt_max is too low:
1. Check smoothing window - try 0.5-1.0 ms
2. Verify sampling rate (>10 kHz recommended)
3. Confirm correct species selection

If smoothing doesn't seem to apply:
• Ensure "Enable smoothing" checkbox is checked
• Set smoothing window > 0 (or leave empty for adaptive)

IMPORTANT: When you set smoothing to 9-10 ms, dV/dt_max remains accurate
because APEX uses a separate minimally-smoothed trace (0.5 ms) for upstroke
detection and derivative calculation. This is done automatically.
"""
        smoothing_scroll.insert(tk.END, smoothing_guide_text)
        smoothing_scroll.config(state=tk.DISABLED)
        
        # Tab 3: Mouse AP Detection Guide
        mouse_frame = ttk.Frame(notebook)
        notebook.add(mouse_frame, text="Mouse AP Guide")
        
        mouse_scroll = scrolledtext.ScrolledText(mouse_frame, wrap=tk.WORD, font=("Courier", 10))
        mouse_scroll.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        mouse_guide = """
MOUSE ACTION POTENTIAL DETECTION GUIDE
======================================

KEY THRESHOLD CHANGES (March 2026)
----------------------------------
• APD90 threshold: 50ms → 15ms (minimum)
• APD30 threshold: 20ms → 2ms (minimum)
• APD50 threshold: 40ms → 2ms (minimum)
• APD90 range updated to (15, 80) ms
• dV/dt_max range maintained at (200-500 mV/ms)

WHY MOUSE APs ARE DIFFERENT
---------------------------
Mouse ventricular action potentials are extremely short compared to other species:

Species Comparison:
• Mouse:   APD90 = 30-60 ms,   APD30 = 5-15 ms,   APD50 = 15-35 ms
• Rabbit:  APD90 = 150-250 ms, APD30 = 50-80 ms,  APD50 = 80-120 ms
• Human:   APD90 = 250-350 ms, APD30 = 80-120 ms, APD50 = 150-200 ms

CRITICAL: Mouse APs have no plateau phase and repolarize almost immediately.
The short APD30/APD50 values are NORMAL and should NOT be rejected as artifacts.

VALID MOUSE AP CRITERIA
-----------------------
✓ APA > 20 mV (typical: 40-80 mV)
✓ dV/dt_max > 200 mV/ms (typical: 300-500 mV/ms)
✓ APD90 between 15-80 ms (typical: 30-60 ms)
✓ APD30 > 2 ms (typical: 5-15 ms)
✓ APD50 > 2 ms (typical: 15-35 ms)
✓ Clear upstroke and repolarization phase
✓ Stable baseline RMP (-80 to -70 mV)

WHAT ARE ARTIFACTS vs REAL MOUSE APs?
-------------------------------------
Artifact (Reject):
• APD90 < 5 ms AND APA < 10 mV → Stimulation artifact
• No clear upstroke (dV/dt_max < 100 mV/ms)
• Flat line after peak (no repolarization)
• Random noise without consistent morphology

Valid Mouse AP (Accept):
• APD90 = 15-80 ms
• APD30 = 5-15 ms (sometimes as low as 2-3 ms!)
• APD50 = 15-35 ms
• dV/dt_max = 300-500 mV/ms
• Clear exponential repolarization
• Consistent morphology across beats

RECOMMENDED SETTINGS FOR MOUSE
------------------------------
• Species: Mouse (select from dropdown)
• Smoothing: 0.6 ms (adaptive by default)
• Min APD90: Leave at default (auto-detected)
• Dual-path detection: Enabled
• Corrected APD80/90: Enabled

TROUBLESHOOTING MOUSE DETECTION
------------------------------
If mouse APs are still being rejected:
1. Check species selection → Must be "Mouse"
2. Verify APD90 > 15 ms → If <15 ms, may be stimulation artifact
3. Check dV/dt_max > 200 mV/ms → If lower, check sampling rate
4. Review raw data quality → Excessive noise affects detection
5. Try manual peak selection → Interactive mode for problematic traces

If you see warnings about short APD30/APD50:
• IGNORE these warnings for mouse data
• The thresholds are now set appropriately (2 ms minimum)
• Your mouse data is likely correct

SAMPLING RATE REQUIREMENTS
-------------------------
For accurate mouse AP analysis:
• Minimum: 10 kHz (100 μs resolution)
• Recommended: 20-50 kHz (20-50 μs resolution)
• Higher rates needed for accurate dV/dt_max

Why? Mouse upstrokes are extremely fast (dV/dt_max 300-500 mV/ms)
requiring high temporal resolution for accurate measurement.

EXPORT NOTES
------------
When exporting mouse data:
• APD values will appear very short (30-60 ms) - This is NORMAL
• Compare to control conditions, not to rabbit/human values
• STV will be calculated on mouse-scale values
• Use Poincaré plots to assess beat-to-beat variability

REFERENCE VALUES
---------------
Normal mouse ventricular AP parameters:
• RMP: -80 to -70 mV
• APA: 40-80 mV
• APD90: 30-60 ms
• APD30: 5-15 ms
• APD50: 15-35 ms
• dV/dt_max: 300-500 mV/ms
• Repolarization Fraction: 0.4-0.6

Drug effects on mouse APs:
• Class III (IKr blockers): Small APD prolongation (unlike rabbit)
• Class I (Na+ blockers): Reduced dV/dt_max, slowed conduction
• Calcium blockers: Reduced APA, shortened APD

For more information, refer to:
• Nerbonne, J.M. (2018) Mouse models of cardiac arrhythmias
• London, B. (2002) Mouse models of long QT syndrome
"""
        
        mouse_scroll.insert(tk.END, mouse_guide)
        mouse_scroll.config(state=tk.DISABLED)
        
        # Tab 4: Cardioid Immature Mode Guide
        cardioid_frame = ttk.Frame(notebook)
        notebook.add(cardioid_frame, text="Cardioid Immature Mode")
        
        cardioid_scroll = scrolledtext.ScrolledText(cardioid_frame, wrap=tk.WORD, font=("Courier", 10))
        cardioid_scroll.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        cardioid_guide = """
CARDIOD IMMATURE MODE GUIDE
===========================

WHAT IS CARDIOD IMMATURE MODE?
-------------------------------
Cardioids (stem cell-derived cardiomyocytes) from early differentiation weeks have:
• Very large stimulation artifacts due to higher pacing currents needed
• Low amplitude APs (APA sometimes < 20 mV)
• Short APD90 (sometimes < 50 ms, can be as low as 30-40 ms)
• Noisy signal requiring aggressive smoothing (9-10 ms)
• Poor automatic peak detection

Immature Mode lowers the acceptance thresholds to properly detect these early-stage APs.

WHEN TO USE IMMATURE MODE
-------------------------
Enable "Cardioid Immature Mode" when:
• Working with early-differentiation cardioids (week 2-4)
• APA is consistently < 20 mV
• APD90 is < 50 ms
• APs are being rejected despite manual peak selection
• dV/dt_max validation fails (outside 100-450 range)

DO NOT use Immature Mode for:
• Mature cardioids (week 6+)
• Other species (rabbit, mouse, zebrafish)
• Normal adult cardiomyocytes

THRESHOLD CHANGES IN IMMATURE MODE
----------------------------------
Parameter        | Normal Mode | Immature Mode
-----------------|-------------|---------------
Min APA          | 15 mV       | 10 mV
Min APD90        | 50 ms       | 25 ms
Min dV/dt_max    | 10 mV/ms    | 5 mV/ms
Max APD90        | 500 ms      | 500 ms
APD30/APD50      | Same        | Same

WHAT HAPPENS WHEN YOU ENABLE IMMATURE MODE
------------------------------------------
1. AP validation uses lower thresholds:
   - APA from 15 mV → 10 mV
   - APD90 from 50 ms → 25 ms
   - dV/dt_max from 10 mV/ms → 5 mV/ms

2. dV/dt_max validation is bypassed for cardioid APs
   (or uses much wider acceptable range)

3. Stimulation artifact detection is adjusted:
   - Larger search window after stimulation (up to 400ms)
   - Lower stimulation artifact detection prominence

4. Adaptive smoothing suggests 5-10 ms window
   (a message will appear when Immature Mode is selected)

TROUBLESHOOTING WITH IMMATURE MODE
----------------------------------
If APs are still being rejected:
1. Try manual peak selection first
2. If dV/dt_max is still outside range, the software will prompt you to:
   a) Accept the current value and keep the AP
   b) Manually select upstroke start
   c) Reject this AP

This gives you control over borderline cases.

RECOMMENDED SETTINGS FOR IMMATURE CARDIOD
----------------------------------------
• Species: Cardioid
• Cardioid Immature Mode: Checked ✓
• Smoothing: 5-10 ms (or leave empty for adaptive)
• Min APD90: Leave at default
• Dual-path detection: Enabled
• Corrected APD80/90: Enabled

EXPECTED VALUES FOR IMMATURE CARDIOD
-----------------------------------
• APA: 10-30 mV
• APD90: 25-200 ms
• dV/dt_max: 5-100 mV/ms
• RMP: -80 to -30 mV

As cells mature, these values will approach:
• APA: 40-80 mV
• APD90: 100-300 ms
• dV/dt_max: 100-300 mV/ms

NOTE: Immature Mode is SPECIFIC to cardioid species.
If species is not set to "Cardioid", this option has no effect.
"""
        
        cardioid_scroll.insert(tk.END, cardioid_guide)
        cardioid_scroll.config(state=tk.DISABLED)
        
        # Close button
        ttk.Button(self, text="Close", command=self.destroy, width=15).pack(pady=10)


# ============================================================================
# Interactive Upstroke Start Selector (with selective batch correction)
# ============================================================================

class UpstrokeStartSelector:
    """
    Draggable vertical cursor for upstroke-start selection.

    Usage:
        • Move the mouse over the axes — a vertical cursor follows it.
        • The cursor snaps onto the (minimally-smoothed) trace and shows
          the current time / voltage as a live read-out.
        • Left-click anywhere to lock in the current position.
        • ← / → keys nudge by one sample.
        • Enter accepts, Escape cancels.
        • A second left-click unlocks for fine-tuning.
    """

    def __init__(self, ax, canvas, trace_data, all_results, current_idx, callback=None):
        self.ax = ax
        self.canvas = canvas
        self.trace_data = trace_data
        self.all_results = all_results
        self.current_idx = current_idx
        self.callback = callback

        self.cursor_line = None
        self.cursor_marker = None
        self.cursor_text = None
        self.selected_idx = None
        self.selected_point = None
        self.is_locked = False

        if 'voltage_minimal_smooth' in self.trace_data:
            self._voltage = self.trace_data['voltage_minimal_smooth']
        else:
            self._voltage = self.trace_data['voltage_smooth']
        self._time = self.trace_data['time']

        self.motion_cid = self.canvas.mpl_connect('motion_notify_event', self.on_motion)
        self.click_cid  = self.canvas.mpl_connect('button_press_event',  self.on_click)
        self.key_cid    = self.canvas.mpl_connect('key_press_event',     self.on_key)

        self.marker_color = '#FF6B6B'
        self.line_color   = '#FF6B6B'

    def on_motion(self, event):
        if self.is_locked:
            return
        if event.inaxes != self.ax or event.xdata is None:
            return
        idx = int(np.argmin(np.abs(self._time - event.xdata)))
        if idx < 0 or idx >= len(self._time):
            return
        self.selected_idx = idx
        self.selected_point = (self._time[idx], self._voltage[idx])
        self._draw_cursor()

    def on_click(self, event):
        if event.inaxes != self.ax or event.xdata is None:
            return
        if event.button != 1:
            return
        idx = int(np.argmin(np.abs(self._time - event.xdata)))
        if idx < 0 or idx >= len(self._time):
            return
        self.selected_idx = idx
        self.selected_point = (self._time[idx], self._voltage[idx])
        self._draw_cursor()
        if self.is_locked:
            self.is_locked = False
            return
        self.is_locked = True
        self.show_confirmation_dialog()

    def on_key(self, event):
        if event.key == 'escape':
            self.clear()
        elif event.key == 'enter' and self.selected_idx is not None:
            self.is_locked = True
            self.show_confirmation_dialog()
        elif event.key in ('left', 'right') and self.selected_idx is not None:
            step = -1 if event.key == 'left' else 1
            new_idx = max(0, min(len(self._time) - 1, self.selected_idx + step))
            self.selected_idx = new_idx
            self.selected_point = (self._time[new_idx], self._voltage[new_idx])
            self._draw_cursor()

    def _draw_cursor(self):
        if self.selected_point is None:
            return
        t_pt, v_pt = self.selected_point
        for artist in (self.cursor_line, self.cursor_marker, self.cursor_text):
            if artist is not None:
                try:
                    artist.remove()
                except Exception:
                    pass
        y_min, y_max = self.ax.get_ylim()
        self.cursor_line = self.ax.axvline(
            x=t_pt, color=self.line_color, linestyle='--',
            linewidth=1.5, alpha=0.85, zorder=9
        )
        self.cursor_marker = self.ax.scatter(
            [t_pt], [v_pt], s=110, c=self.marker_color, marker='D',
            edgecolors='darkred', linewidths=1.5, zorder=10
        )
        self.cursor_text = self.ax.text(
            t_pt, y_max - (y_max - y_min) * 0.05,
            f'Upstroke start\n{t_pt:.2f} ms  |  {v_pt:.1f} mV\n(click to confirm)',
            fontsize=8, ha='center', va='top',
            bbox=dict(boxstyle='round,pad=0.3',
                      facecolor='white', edgecolor=self.line_color, alpha=0.9),
            zorder=11
        )
        self.canvas.draw_idle()

    def show_confirmation_dialog(self):
        if self.selected_point is None:
            return
        upstroke_time, upstroke_voltage = self.selected_point

        current_trace = self.all_results[self.current_idx]
        peak_time = 0
        peak_idx = 0
        if current_trace.get('ap_metrics'):
            current_ap = current_trace['ap_metrics'][0]
            peak_time = current_ap.get('peak_time', 0)
            peak_idx = current_ap.get('peak_idx', 0)

        time = self.trace_data['time']
        dt = time[1] - time[0] if len(time) > 1 else 0.1
        dvdt_max, _ = calculate_dvdt_from_points(
            self._voltage, time, self.selected_idx, peak_idx, dt,
            is_manual_selection=True
        )

        dt_ms = self.trace_data.get('dt_ms', 0.1)
        similar_aps = find_similar_aps_by_morphology(
            current_ap if current_trace.get('ap_metrics') else {},
            self.all_results, self.current_idx, 0,
            threshold=0.70, dt_ms=dt_ms
        )

        dialog = tk.Toplevel(self.canvas.get_tk_widget().master)
        dialog.title("Confirm Upstroke Start")
        dialog.geometry("650x550")
        dialog.transient(self.canvas.get_tk_widget().master)
        dialog.grab_set()
        dialog.configure(bg='white')

        ttk.Label(dialog, text="Confirm Upstroke Start Point",
                  font=("Helvetica", 12, "bold")).pack(pady=10)

        info = ttk.LabelFrame(dialog, text="Selected Point Details", padding=10)
        info.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(info, text=f"Time: {upstroke_time:.2f} ms").pack(anchor='w', pady=2)
        ttk.Label(info, text=f"Voltage: {upstroke_voltage:.2f} mV").pack(anchor='w', pady=2)
        ttk.Label(info, text=f"Peak Time: {peak_time:.2f} ms").pack(anchor='w', pady=2)
        ttk.Label(info, text=f"Upstroke Duration: {peak_time - upstroke_time:.2f} ms").pack(anchor='w', pady=2)

        dv = ttk.LabelFrame(dialog, text="dV/dt_max Calculation", padding=10)
        dv.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(dv, text=f"Calculated dV/dt_max: {dvdt_max:.1f} mV/ms",
                  font=("Helvetica", 10, "bold")).pack(anchor='w', pady=2)

        self.batch_apply_var = tk.BooleanVar(value=False)
        if similar_aps:
            bf = ttk.LabelFrame(dialog, text="Apply to Similar APs", padding=10)
            bf.pack(fill=tk.X, padx=10, pady=5)
            ttk.Label(bf, text=f"Found {len(similar_aps)} APs with similar morphology.",
                      font=("Helvetica", 10)).pack(anchor='w', pady=2)
            ttk.Checkbutton(bf,
                            text="Apply this upstroke correction to similar APs (selective)",
                            variable=self.batch_apply_var).pack(anchor='w', pady=5)

        btns = ttk.Frame(dialog)
        btns.pack(pady=20)

        def confirm():
            dialog.destroy()
            if self.callback:
                batch_apply = self.batch_apply_var.get() if hasattr(self, 'batch_apply_var') else False
                self.callback(self.selected_idx, upstroke_time, upstroke_voltage,
                              dvdt_max, batch_apply)
            self.clear()

        def cancel():
            dialog.destroy()
            self.is_locked = False
            self.clear()

        ttk.Button(btns, text="Apply",  command=confirm, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(btns, text="Cancel", command=cancel,  width=15).pack(side=tk.LEFT, padx=5)

    def clear(self):
        for artist in (self.cursor_line, self.cursor_marker, self.cursor_text):
            if artist is not None:
                try:
                    artist.remove()
                except Exception:
                    pass
        self.cursor_line = self.cursor_marker = self.cursor_text = None

        for cid in (self.motion_cid, self.click_cid, self.key_cid):
            if cid:
                try:
                    self.canvas.mpl_disconnect(cid)
                except Exception:
                    pass
        self.motion_cid = self.click_cid = self.key_cid = None

        self.selected_idx = None
        self.selected_point = None
        self.canvas.draw_idle()


# ============================================================================
# Enhanced Interactive Peak Selector (with selective batch correction)
# ============================================================================

class EnhancedInteractivePeakSelector:
    """Enhanced interactive peak selection with upstroke support and selective batch correction"""
    
    def __init__(self, ax, canvas, trace_data, all_results, current_idx, callback=None):
        self.ax = ax
        self.canvas = canvas
        self.trace_data = trace_data
        self.all_results = all_results
        self.current_idx = current_idx
        self.callback = callback
        
        self.draggable_marker = None
        self.selected_peak_idx = None
        self.selected_peak_point = None
        self.is_dragging = False
        self.drag_offset = (0, 0)
        
        self.click_cid = self.canvas.mpl_connect('button_press_event', self.on_click)
        self.drag_cid = self.canvas.mpl_connect('motion_notify_event', self.on_motion)
        self.release_cid = self.canvas.mpl_connect('button_release_event', self.on_release)
        self.key_cid = self.canvas.mpl_connect('key_press_event', self.on_key)
        
        self.marker_color = '#FF6B6B'
        self.marker_size = 120
        self.marker_alpha = 0.9
    
    def on_click(self, event):
        if event.inaxes != self.ax:
            return
        
        if event.button == 1:
            if self.draggable_marker is not None:
                marker_pos = self.draggable_marker.get_offsets()[0]
                dist = np.sqrt((event.xdata - marker_pos[0]) ** 2 + (event.ydata - marker_pos[1]) ** 2)
                if dist < 0.05:
                    self.is_dragging = True
                    self.drag_offset = (event.xdata - marker_pos[0], event.ydata - marker_pos[1])
                    return
            
            time = self.trace_data['time']
            # Use minimally-smoothed trace for peak selection if available
            if 'voltage_minimal_smooth' in self.trace_data:
                voltage = self.trace_data['voltage_minimal_smooth']
            else:
                voltage = self.trace_data['voltage_smooth']
            
            if len(time) == 0 or len(voltage) == 0:
                return
            
            distances = np.sqrt((time - event.xdata) ** 2 + (voltage - event.ydata) ** 2)
            closest_idx = np.argmin(distances)
            
            self.selected_peak_idx = closest_idx
            self.selected_peak_point = (time[closest_idx], voltage[closest_idx])
            
            self.update_marker()
            self.show_simple_dialog()
    
    def show_simple_dialog(self):
        """Show simple dialog for peak confirmation with selective batch option"""
        if self.selected_peak_point is None:
            return
        
        peak_time, peak_voltage = self.selected_peak_point
        
        current_trace = self.all_results[self.current_idx]
        current_ap = current_trace['ap_metrics'][0] if current_trace.get('ap_metrics') else None
        
        similar_aps = []
        if current_ap:
            dt_ms = self.trace_data.get('dt_ms', 0.1)
            similar_aps = find_similar_aps_by_morphology(
                current_ap, self.all_results, self.current_idx, 0, 
                threshold=0.70, dt_ms=dt_ms
            )
        
        dialog = tk.Toplevel(self.canvas.get_tk_widget().master)
        dialog.title("Confirm Peak Selection")
        dialog.geometry("500x400")
        dialog.transient(self.canvas.get_tk_widget().master)
        dialog.grab_set()
        dialog.configure(bg='white')
        
        ttk.Label(dialog, text="Confirm AP Peak Selection",
                  font=("Helvetica", 12, "bold")).pack(pady=10)
        
        info_text = f"""
Selected AP Peak:
Time: {peak_time:.1f} ms
Voltage: {peak_voltage:.1f} mV
"""
        ttk.Label(dialog, text=info_text, justify=tk.LEFT, 
                 font=("Helvetica", 10), background='white').pack(pady=10, padx=20)
        
        if similar_aps:
            batch_frame = ttk.LabelFrame(dialog, text="Apply to Similar APs", padding=10)
            batch_frame.pack(fill=tk.X, padx=20, pady=10)
            
            ttk.Label(batch_frame, 
                     text=f"Found {len(similar_aps)} APs with similar morphology.",
                     font=("Helvetica", 10)).pack(anchor='w', pady=2)
            
            ttk.Label(batch_frame, 
                     text="APs with >95% similarity will be automatically selected.",
                     font=("Helvetica", 9, "italic")).pack(anchor='w', pady=2)
            
            self.batch_apply_var = tk.BooleanVar(value=True)
            ttk.Checkbutton(batch_frame, 
                          text=f"Apply this peak correction to similar APs (selective)",
                          variable=self.batch_apply_var).pack(anchor='w', pady=5)
        
        button_frame = ttk.Frame(dialog)
        button_frame.pack(pady=20)
        
        def confirm():
            dialog.destroy()
            if self.callback:
                batch_apply = hasattr(self, 'batch_apply_var') and self.batch_apply_var.get()
                self.callback(self.selected_peak_idx, peak_time, peak_voltage, batch_apply)
            self.clear()
        
        def cancel():
            dialog.destroy()
            self.clear()
        
        ttk.Button(button_frame, text="Apply", command=confirm, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=cancel, width=15).pack(side=tk.LEFT, padx=5)
    
    def on_motion(self, event):
        if not self.is_dragging or event.inaxes != self.ax:
            return
        
        if self.draggable_marker is not None:
            new_x = event.xdata - self.drag_offset[0]
            new_y = event.ydata - self.drag_offset[1]
            
            time = self.trace_data['time']
            if 'voltage_minimal_smooth' in self.trace_data:
                voltage = self.trace_data['voltage_minimal_smooth']
            else:
                voltage = self.trace_data['voltage_smooth']
            
            if len(time) > 0 and len(voltage) > 0:
                distances = np.sqrt((time - new_x) ** 2 + (voltage - new_y) ** 2)
                closest_idx = np.argmin(distances)
                
                self.selected_peak_idx = closest_idx
                self.selected_peak_point = (time[closest_idx], voltage[closest_idx])
                
                self.draggable_marker.set_offsets([[time[closest_idx], voltage[closest_idx]]])
                self.canvas.draw_idle()
    
    def on_release(self, event):
        if event.button == 1:
            self.is_dragging = False
    
    def on_key(self, event):
        if event.key == 'escape':
            self.clear()
        elif event.key == 'enter' and self.selected_peak_idx is not None:
            self.show_simple_dialog()
    
    def update_marker(self):
        if self.selected_peak_point is None:
            return
        
        if self.draggable_marker is not None:
            try:
                self.draggable_marker.remove()
            except:
                self.draggable_marker.set_offsets(np.empty((0, 2)))
        
        self.draggable_marker = self.ax.scatter(
            [self.selected_peak_point[0]], [self.selected_peak_point[1]],
            s=self.marker_size, c=self.marker_color, marker='D',
            edgecolors='darkred', linewidths=2, alpha=self.marker_alpha,
            zorder=10, picker=True, label='Selected Peak'
        )
        
        if hasattr(self, 'marker_text'):
            try:
                self.marker_text.remove()
            except:
                pass
        
        self.marker_text = self.ax.text(
            self.selected_peak_point[0], self.selected_peak_point[1] + 5,
            f'Selected\n{self.selected_peak_point[1]:.1f} mV',
            fontsize=9, ha='center', va='bottom',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.9)
        )
        
        self.canvas.draw_idle()
    
    def clear(self):
        if self.draggable_marker is not None:
            try:
                self.draggable_marker.remove()
            except:
                self.draggable_marker.set_offsets(np.empty((0, 2)))
            self.draggable_marker = None
        
        if hasattr(self, 'marker_text'):
            try:
                self.marker_text.remove()
            except:
                pass
            delattr(self, 'marker_text')
        
        self.selected_peak_idx = None
        self.selected_peak_point = None
        self.is_dragging = False
        
        if self.click_cid:
            self.canvas.mpl_disconnect(self.click_cid)
            self.click_cid = None
        if self.drag_cid:
            self.canvas.mpl_disconnect(self.drag_cid)
            self.drag_cid = None
        if self.release_cid:
            self.canvas.mpl_disconnect(self.release_cid)
            self.release_cid = None
        if self.key_cid:
            self.canvas.mpl_disconnect(self.key_cid)
            self.key_cid = None
        
        self.canvas.draw_idle()


# ============================================================================
# ABF Range Selection Dialog
# ============================================================================

class ABFRangeSelectionDialog(tk.Toplevel):
    """Enhanced ABF range selection with multiple ranges and drug assignment"""
    
    def __init__(self, parent, filename, sweep_count):
        super().__init__(parent)
        self.parent = parent
        self.filename = filename
        self.sweep_count = sweep_count
        self.ranges = []
        
        self.title(f"ABF Range Selection - {Path(filename).name}")
        self.geometry("700x500")
        self.transient(parent)
        self.grab_set()
        
        self.configure(bg='white')
        
        header = ttk.Label(self, text=f"Select Ranges for {Path(filename).name}",
                           font=("Helvetica", 12, "bold"), background='white')
        header.pack(pady=10)
        
        ttk.Label(self, text=f"Total sweeps: {sweep_count}", font=("Helvetica", 10)).pack()
        
        main_frame = ttk.Frame(self)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        canvas = tk.Canvas(main_frame)
        scrollbar = ttk.Scrollbar(main_frame, orient=tk.VERTICAL, command=canvas.yview)
        self.scrollable_frame = ttk.Frame(canvas)
        
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.create_range_entry_section()
        self.create_ranges_display()
        
        button_frame = ttk.Frame(self)
        button_frame.pack(pady=10)
        
        ttk.Button(button_frame, text="Done", command=self.save_ranges, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=self.cancel, width=15).pack(side=tk.LEFT, padx=5)
    
    def create_range_entry_section(self):
        """Create section for entering new ranges"""
        entry_frame = ttk.LabelFrame(self.scrollable_frame, text="Add New Range", padding=10)
        entry_frame.pack(fill=tk.X, pady=10)
        
        range_frame = ttk.Frame(entry_frame)
        range_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(range_frame, text="Sweep Range (e.g., 1-20):").pack(side=tk.LEFT, padx=5)
        self.range_var = tk.StringVar()
        range_entry = ttk.Entry(range_frame, textvariable=self.range_var, width=15)
        range_entry.pack(side=tk.LEFT, padx=5)
        
        drug_frame = ttk.Frame(entry_frame)
        drug_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(drug_frame, text="Drug/Condition:").pack(side=tk.LEFT, padx=5)
        self.drug_var = tk.StringVar(value="None")
        drug_combo = ttk.Combobox(drug_frame, textvariable=self.drug_var,
                                  values=COMMON_DRUGS, state="readonly", width=15)
        drug_combo.pack(side=tk.LEFT, padx=5)
        
        self.custom_drug_frame = ttk.Frame(drug_frame)
        ttk.Label(self.custom_drug_frame, text="Custom drug:").pack(side=tk.LEFT, padx=5)
        self.custom_drug_var = tk.StringVar()
        ttk.Entry(self.custom_drug_frame, textvariable=self.custom_drug_var, width=15).pack(side=tk.LEFT, padx=5)
        
        def on_drug_selected(event):
            if self.drug_var.get() == "Other":
                self.custom_drug_frame.pack(side=tk.LEFT, padx=5)
            else:
                self.custom_drug_frame.pack_forget()
        
        drug_combo.bind('<<ComboboxSelected>>', on_drug_selected)
        
        conc_frame = ttk.Frame(entry_frame)
        conc_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(conc_frame, text="Concentration (optional):").pack(side=tk.LEFT, padx=5)
        self.conc_var = tk.StringVar()
        ttk.Entry(conc_frame, textvariable=self.conc_var, width=15).pack(side=tk.LEFT, padx=5)
        
        desc_frame = ttk.Frame(entry_frame)
        desc_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(desc_frame, text="Description:").pack(side=tk.LEFT, padx=5)
        self.desc_var = tk.StringVar()
        ttk.Entry(desc_frame, textvariable=self.desc_var, width=30).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(entry_frame, text="Add Range", command=self.add_range).pack(pady=10)
    
    def add_range(self):
        """Add a new range to the list"""
        try:
            range_str = self.range_var.get().strip()
            if not range_str:
                messagebox.showwarning("Input Error", "Please enter a range")
                return
            
            if '-' in range_str:
                start, end = map(int, range_str.split('-'))
            else:
                start = end = int(range_str)
            
            if not (1 <= start <= end <= self.sweep_count):
                messagebox.showwarning("Range Error",
                                       f"Range must be between 1 and {self.sweep_count}")
                return
            
            name = f"{start}-{end}"
            drug = self.drug_var.get()
            if drug == "Other":
                drug = self.custom_drug_var.get().strip()
                if not drug:
                    messagebox.showwarning("Input Error", "Please enter a custom drug name when selecting 'Other'")
                    return
            conc = self.conc_var.get().strip()
            desc = self.desc_var.get().strip()
            
            range_info = {
                'name': name,
                'range': (start - 1, end - 1),
                'drug': drug,
                'concentration': conc,
                'description': desc
            }
            
            self.ranges.append(range_info)
            
            self.ranges_tree.insert('', tk.END, values=(
                f"{start}-{end}",
                f"{end - start + 1} sweeps",
                name,
                drug,
                conc,
                desc
            ))
            
            self.range_var.set("")
            self.drug_var.set("None")
            self.conc_var.set("")
            self.desc_var.set("")
        
        except ValueError:
            messagebox.showwarning("Input Error", "Please enter valid numbers for range")
    
    def create_ranges_display(self):
        """Create display for existing ranges"""
        self.ranges_frame = ttk.LabelFrame(self.scrollable_frame, text="Selected Ranges", padding=10)
        self.ranges_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        columns = ("Range", "Sweeps", "Name", "Drug", "Concentration", "Description")
        self.ranges_tree = ttk.Treeview(self.ranges_frame, columns=columns, show='headings', height=5)
        
        for col in columns:
            self.ranges_tree.heading(col, text=col)
            self.ranges_tree.column(col, width=80)
        
        tree_scroll = ttk.Scrollbar(self.ranges_frame, orient=tk.VERTICAL, command=self.ranges_tree.yview)
        self.ranges_tree.configure(yscrollcommand=tree_scroll.set)
        
        self.ranges_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        ttk.Button(self.ranges_frame, text="Remove Selected", command=self.remove_range).pack(pady=5)
    
    def remove_range(self):
        """Remove selected range"""
        selection = self.ranges_tree.selection()
        if not selection:
            return
        
        for item in selection:
            index = self.ranges_tree.index(item)
            if 0 <= index < len(self.ranges):
                self.ranges.pop(index)
            self.ranges_tree.delete(item)
    
    def save_ranges(self):
        """Save ranges and close dialog"""
        if not self.ranges:
            response = messagebox.askyesno("No Ranges",
                                           "No ranges selected. Import all sweeps?")
            if response:
                self.ranges = [{
                    'name': 'All',
                    'range': (0, self.sweep_count - 1),
                    'drug': 'None',
                    'concentration': '',
                    'description': 'All sweeps'
                }]
            else:
                return
        
        self.destroy()
    
    def cancel(self):
        """Cancel range selection"""
        self.ranges = None
        self.destroy()
    
    def get_ranges(self):
        """Return selected ranges"""
        return self.ranges


# ============================================================================
# Enhanced Excel Stacking Dialog (FIXED for cell grouping)
# ============================================================================

class EnhancedExcelStackerDialog(tk.Toplevel):
    """Enhanced Excel stacking with automatic frequency detection and manual grouping"""
    
    def __init__(self, parent, file_paths, file_metadata=None):
        super().__init__(parent)
        self.parent = parent
        self.file_paths = file_paths
        self.file_metadata = file_metadata or {}
        self.stack_groups = defaultdict(list)
        self.manual_group_info = {}
        self.result = {"stacked_data": {}, "grouping_info": {}}
        
        self.expanded_file_list = []
        
        self.title("APEX - Enhanced Excel Stacking")
        self.geometry("900x700")
        self.transient(parent)
        self.grab_set()
        
        self.configure(bg='white')
        
        header = ttk.Label(self, text="Enhanced Excel File Stacking", 
                          font=("Helvetica", 14, "bold"), background='white')
        header.pack(pady=15)
        
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.create_auto_detection_tab()
        self.create_manual_grouping_tab()
        self.create_summary_tab()
        
        button_frame = ttk.Frame(self)
        button_frame.pack(pady=10)
        
        ttk.Button(button_frame, text="Stack Files", command=self.stack_files, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Export Stacked", command=self.export_stacked, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=self.cancel, width=15).pack(side=tk.LEFT, padx=5)
    
    def create_auto_detection_tab(self):
        auto_tab = ttk.Frame(self.notebook)
        self.notebook.add(auto_tab, text="Auto Detection")
        
        ttk.Label(auto_tab, text="Auto-detect and stack files by cell and frequency:", 
                 font=("Helvetica", 10)).pack(pady=10)
        
        ttk.Button(auto_tab, text="Detect Patterns", command=self.detect_patterns, 
                  width=20).pack(pady=10)
        
        results_frame = ttk.LabelFrame(auto_tab, text="Detection Results", padding=10)
        results_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.auto_results_text = scrolledtext.ScrolledText(results_frame, height=15, width=80)
        self.auto_results_text.pack(fill=tk.BOTH, expand=True)
    
    def create_manual_grouping_tab(self):
        manual_tab = ttk.Frame(self.notebook)
        self.notebook.add(manual_tab, text="Manual Grouping")
        
        self.expand_multi_sheet_files()
        
        list_frame = ttk.LabelFrame(manual_tab, text="Select Files to Group", padding=10)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        refresh_frame = ttk.Frame(list_frame)
        refresh_frame.pack(fill=tk.X, pady=5)
        ttk.Button(refresh_frame, text="Refresh from Metadata", 
                  command=self.refresh_from_metadata, width=20).pack(side=tk.RIGHT, padx=5)
        
        columns = ("Select", "File", "Sheet", "Type", "Cell ID", "Frequency", "Drug", "Condition")
        self.file_tree = ttk.Treeview(list_frame, columns=columns, show='headings', height=10)
        
        for col in columns:
            self.file_tree.heading(col, text=col)
            self.file_tree.column(col, width=90)
        
        tree_scroll = ttk.Scrollbar(list_frame, orient=tk.VERTICAL, command=self.file_tree.yview)
        self.file_tree.configure(yscrollcommand=tree_scroll.set)
        
        self.file_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        for file_info in self.expanded_file_list:
            self.add_file_to_tree(file_info)
        
        group_frame = ttk.LabelFrame(manual_tab, text="Create Manual Stack", padding=10)
        group_frame.pack(fill=tk.X, padx=10, pady=10)
        
        ttk.Label(group_frame, text="Stack Name:").pack(anchor='w', pady=2)
        self.group_name_var = tk.StringVar(value="Stack_1")
        ttk.Entry(group_frame, textvariable=self.group_name_var, width=30).pack(fill=tk.X, pady=2)
        
        ttk.Label(group_frame, text="Cell ID for this stack:").pack(anchor='w', pady=2)
        self.group_cell_id_var = tk.StringVar(value="Cell_1")
        ttk.Entry(group_frame, textvariable=self.group_cell_id_var, width=30).pack(fill=tk.X, pady=2)
        
        ttk.Label(group_frame, text="Frequency (Hz):").pack(anchor='w', pady=2)
        self.group_freq_var = tk.StringVar(value="1.0")
        freq_combo = ttk.Combobox(group_frame, textvariable=self.group_freq_var, 
                                 values=['0.5', '1.0', '2.0', '3.0', '4.0', '5.0', 'Unknown'], 
                                 state="readonly", width=30)
        freq_combo.pack(fill=tk.X, pady=2)
        
        ttk.Label(group_frame, text="Drug/Condition:").pack(anchor='w', pady=2)
        self.group_drug_var = tk.StringVar(value="None")
        drug_combo = ttk.Combobox(group_frame, textvariable=self.group_drug_var, 
                                 values=COMMON_DRUGS, state="readonly", width=30)
        drug_combo.pack(fill=tk.X, pady=2)
        
        ttk.Label(group_frame, text="Concentration (optional):").pack(anchor='w', pady=2)
        self.group_conc_var = tk.StringVar()
        ttk.Entry(group_frame, textvariable=self.group_conc_var, width=30).pack(fill=tk.X, pady=2)
        
        btn_frame = ttk.Frame(group_frame)
        btn_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(btn_frame, text="Create Stack", command=self.create_manual_group, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Clear Selection", command=self.clear_selection, width=15).pack(side=tk.LEFT, padx=5)
    
    def create_summary_tab(self):
        summary_tab = ttk.Frame(self.notebook)
        self.notebook.add(summary_tab, text="Stack Summary")
        
        ttk.Label(summary_tab, text="Stacks Created:", font=("Helvetica", 11, "bold")).pack(pady=10)
        
        self.summary_text = scrolledtext.ScrolledText(summary_tab, height=20, width=80)
        self.summary_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.summary_text.insert(tk.END, "No stacks created yet.\n\n")
        self.summary_text.insert(tk.END, "Instructions:\n")
        self.summary_text.insert(tk.END, "1. Use Auto Detection or Manual Grouping tabs\n")
        self.summary_text.insert(tk.END, "2. Create stacks with appropriate metadata\n")
        self.summary_text.insert(tk.END, "3. View stack summary here\n")
        self.summary_text.insert(tk.END, "4. Click 'Stack Files' to process\n")
        self.summary_text.config(state=tk.DISABLED)
    
    def add_file_to_tree(self, file_info):
        file_path = file_info['file_path']
        path = Path(file_path)
        sheet_name = file_info.get('sheet_name', '')
        display_name = file_info.get('display_name', path.name)
        file_type = file_info['file_type']
        
        cell_id = file_info.get('cell_id', 'Unknown')
        frequency = file_info.get('frequency', 'Unknown')
        drug = file_info.get('drug', 'None')
        concentration = file_info.get('concentration', '')
        
        condition_display = f"{drug}"
        if concentration:
            condition_display += f" ({concentration})"
        
        self.file_tree.insert('', tk.END, values=(
            "",
            display_name,
            sheet_name if sheet_name else "-",
            file_type,
            cell_id,
            frequency,
            drug,
            condition_display
        ))
    
    def expand_multi_sheet_files(self):
        """Expand multi-sheet Excel files into separate entries per sheet"""
        self.expanded_file_list = []
        
        for file_path in self.file_paths:
            path = Path(file_path)
            meta = self.file_metadata.get(file_path, {})
            has_metadata = bool(meta.get('cell_id') and meta.get('cell_id') != 'Unknown' and meta.get('cell_id') != 'Cell_Unknown')
            
            if path.suffix in ['.xlsx', '.xls']:
                try:
                    excel_file = pd.ExcelFile(file_path)
                    sheet_names = excel_file.sheet_names
                    
                    for sheet_name in sheet_names:
                        if has_metadata:
                            cell_id = meta.get('cell_id', 'Cell_Unknown')
                            frequency = meta.get('frequency', '1.0')
                            drug = meta.get('drug', 'None')
                            concentration = meta.get('concentration', '')
                            species = meta.get('species', 'default')
                        else:
                            cell_id = self.extract_cell_id(sheet_name)
                            frequency = self.extract_frequency(sheet_name)
                            condition = self.extract_condition(sheet_name)
                            drug = condition if condition in COMMON_DRUGS else 'None'
                            concentration = ''
                            species = 'default'
                        
                        self.expanded_file_list.append({
                            'file_path': file_path,
                            'sheet_name': sheet_name,
                            'frequency': frequency,
                            'cell_id': cell_id,
                            'drug': drug,
                            'concentration': concentration,
                            'species': species,
                            'file_type': 'Excel',
                            'display_name': f"{path.name} [{sheet_name}]"
                        })
                        
                except Exception as e:
                    print(f"Error reading Excel file {file_path}: {e}")
                    self.add_single_file_entry(file_path, meta)
            else:
                self.add_single_file_entry(file_path, meta)
    
    def add_single_file_entry(self, file_path, meta):
        path = Path(file_path)
        has_metadata = bool(meta.get('cell_id') and meta.get('cell_id') != 'Unknown' and meta.get('cell_id') != 'Cell_Unknown')
        
        if has_metadata:
            cell_id = meta.get('cell_id', 'Cell_Unknown')
            frequency = meta.get('frequency', '1.0')
            drug = meta.get('drug', 'None')
            concentration = meta.get('concentration', '')
            species = meta.get('species', 'default')
        else:
            # Try PatchMaster extraction
            pm_meta = extract_patchmaster_metadata(path.name)
            cell_id = pm_meta['cell_id']
            frequency = pm_meta['frequency']
            drug = pm_meta['drug']
            concentration = ''
            species = 'default'
        
        self.expanded_file_list.append({
            'file_path': file_path,
            'sheet_name': None,
            'frequency': frequency,
            'cell_id': cell_id,
            'drug': drug,
            'concentration': concentration,
            'species': species,
            'file_type': 'CSV' if path.suffix == '.csv' else 'Excel',
            'display_name': path.name
        })
    
    def refresh_from_metadata(self):
        for item in self.file_tree.get_children():
            self.file_tree.delete(item)
        
        self.expand_multi_sheet_files()
        
        for file_info in self.expanded_file_list:
            self.add_file_to_tree(file_info)
        
        messagebox.showinfo("Refresh Complete", 
                           "File list refreshed with current metadata.\n"
                           "You can now create stacks using the updated information.")
    
    def detect_patterns(self):
        """Auto-detect patterns with proper cell grouping"""
        self.auto_results_text.delete(1.0, tk.END)
        
        self.expand_multi_sheet_files()
        
        # CRITICAL FIX: Group by cell ID, then by frequency
        groups = defaultdict(lambda: defaultdict(list))
        
        for file_info in self.expanded_file_list:
            cell_id = file_info.get('cell_id', 'Unknown')
            frequency = file_info.get('frequency', 'Unknown')
            drug = file_info.get('drug', 'None')
            concentration = file_info.get('concentration', '')
            
            # Create condition key that includes drug if present
            condition_key = f"{frequency}Hz"
            if drug and drug != 'None':
                condition_key += f"_{drug}"
                if concentration:
                    condition_key += f"_{concentration}"
            
            groups[cell_id][condition_key].append(file_info)
        
        # Display results
        for cell_id, conditions in groups.items():
            self.auto_results_text.insert(tk.END, f"\nCell: {cell_id}\n")
            self.auto_results_text.insert(tk.END, "-" * 40 + "\n")
            
            for condition_key, files in conditions.items():
                self.auto_results_text.insert(tk.END, f"  Condition: {condition_key} ({len(files)} files)\n")
                for f in files[:3]:
                    sheet_info = f" [{f['sheet_name']}]" if f.get('sheet_name') else ""
                    meta_info = f" [Cell: {f.get('cell_id')}, {f.get('frequency')}Hz, {f.get('drug')}]"
                    self.auto_results_text.insert(tk.END, f"    • {Path(f['file_path']).name}{sheet_info}{meta_info}\n")
                if len(files) > 3:
                    self.auto_results_text.insert(tk.END, f"    ... and {len(files)-3} more\n")
            
            self.auto_results_text.insert(tk.END, "\n")
        
        # Store grouping with full file info
        self.stack_groups.clear()
        for cell_id, conditions in groups.items():
            for condition_key, files in conditions.items():
                group_key = f"{cell_id}_{condition_key}"
                
                parts = condition_key.split('_')
                frequency = parts[0].replace('Hz', '') if parts else '1.0'
                drug = parts[1] if len(parts) > 1 and parts[1] != 'None' else 'None'
                
                self.stack_groups[group_key] = {
                    'files': files,
                    'cell_id': cell_id,
                    'frequency': frequency,
                    'condition': condition_key,
                    'drug': drug,
                    'stacked': True
                }
        
        self.auto_results_text.insert(tk.END, f"\nTotal groups detected: {len(self.stack_groups)}")
        self.update_summary()
    
    def extract_frequency(self, text):
        text_lower = text.lower()
        
        patterns = [
            r'(\d+\.?\d*)\s*hz',
            r'(\d+\.?\d*)hz',
            r'freq[_\-\s]*(\d+\.?\d*)',
            r'(\d+\.?\d*)\s*Hz',
            r'(\d+)hz',
            r'^(\d+\.?\d*)$',
            r'(\d+\.?\d*)\s*hertz',
            r'(\d+\.?\d*)hertz'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, text_lower)
            if match:
                freq = match.group(1)
                try:
                    freq_num = float(freq)
                    if abs(freq_num - 0.5) < 0.1:
                        return "0.5"
                    elif abs(freq_num - 1.0) < 0.1:
                        return "1.0"
                    elif abs(freq_num - 2.0) < 0.1:
                        return "2.0"
                    elif abs(freq_num - 3.0) < 0.1:
                        return "3.0"
                    elif abs(freq_num - 4.0) < 0.1:
                        return "4.0"
                    elif abs(freq_num - 5.0) < 0.1:
                        return "5.0"
                    else:
                        return f"{freq_num:.1f}"
                except:
                    return "1.0"
        
        if 'baseline' in text_lower or 'control' in text_lower:
            return "1.0"
        
        return "Unknown"
    
    def extract_cell_id(self, filename):
        patterns = [
            r'cell[_\-\s]*([a-zA-Z0-9]+)',
            r'c([a-zA-Z0-9]+)',
            r'([a-zA-Z0-9]+)[_\-\s]*cell',
            r'([a-zA-Z0-9]+)[_\-\s]*\d+\.?\d*hz',
            r'^([A-Za-z]+[0-9]+)',
            r'([A-Z][0-9]+[A-Z]?)'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, filename.lower())
            if match:
                return f"Cell_{match.group(1)}"
        
        return "Cell_Unknown"
    
    def extract_condition(self, filename):
        filename_lower = filename.lower()
        
        for drug in COMMON_DRUGS:
            if drug.lower() != 'none' and drug.lower() in filename_lower:
                return drug
        
        if 'baseline' in filename_lower:
            return 'Baseline'
        elif 'control' in filename_lower:
            return 'Control'
        elif 'washout' in filename_lower:
            return 'Washout'
        elif 'drug' in filename_lower:
            return 'Drug'
        
        return 'Unknown'
    
    def extract_drug_from_condition(self, condition_name):
        for drug in COMMON_DRUGS:
            if drug.lower() in condition_name.lower():
                return drug
        return 'None'
    
    def clear_selection(self):
        for item in self.file_tree.selection():
            self.file_tree.selection_remove(item)
    
    def create_manual_group(self):
        selection = self.file_tree.selection()
        if not selection:
            messagebox.showwarning("Selection", "Please select files first")
            return
        
        group_name = self.group_name_var.get()
        if not group_name:
            messagebox.showwarning("Group Name", "Please enter a stack name")
            return
        
        selected_files = []
        sweep_counter = 1
        
        for item in selection:
            values = self.file_tree.item(item)['values']
            if values and len(values) > 1:
                display_name = values[1]
                sheet_name = values[2] if values[2] != "-" else None
                
                for file_info in self.expanded_file_list:
                    if file_info.get('display_name') == display_name:
                        file_info_copy = file_info.copy()
                        file_info_copy['sweep_number'] = sweep_counter
                        selected_files.append(file_info_copy)
                        sweep_counter += 1
                        break
        
        if selected_files:
            cell_id = self.group_cell_id_var.get()
            frequency = self.group_freq_var.get()
            drug = self.group_drug_var.get()
            concentration = self.group_conc_var.get()
            
            self.stack_groups[group_name] = {
                'files': selected_files,
                'cell_id': cell_id,
                'frequency': frequency,
                'drug': drug,
                'concentration': concentration,
                'stacked': True,
                'manual': True
            }
            
            self.manual_group_info[group_name] = {
                'cell_id': cell_id,
                'frequency': frequency,
                'drug': drug,
                'concentration': concentration
            }
            
            for item in selection:
                self.file_tree.set(item, "Select", "✓")
            
            self.update_summary()
            
            messagebox.showinfo("Stack Created", 
                              f"Stack '{group_name}' created with {len(selected_files)} files\n"
                              f"Cell: {cell_id}, Frequency: {frequency} Hz, Drug: {drug}")
            
            self.group_name_var.set(f"Stack_{len(self.stack_groups)+1}")
            self.group_cell_id_var.set(f"Cell_{len(self.stack_groups)+1}")
    
    def update_summary(self):
        self.summary_text.config(state=tk.NORMAL)
        self.summary_text.delete(1.0, tk.END)
        
        if not self.stack_groups:
            self.summary_text.insert(tk.END, "No stacks created yet.\n")
        else:
            self.summary_text.insert(tk.END, f"Total Stacks: {len(self.stack_groups)}\n")
            self.summary_text.insert(tk.END, "="*60 + "\n\n")
            
            for i, (group_name, group_info) in enumerate(self.stack_groups.items()):
                self.summary_text.insert(tk.END, f"Stack {i+1}: {group_name}\n")
                self.summary_text.insert(tk.END, f"  Cell ID: {group_info.get('cell_id', 'Unknown')}\n")
                self.summary_text.insert(tk.END, f"  Frequency: {group_info.get('frequency', 'Unknown')} Hz\n")
                self.summary_text.insert(tk.END, f"  Drug/Condition: {group_info.get('drug', 'None')}\n")
                if group_info.get('concentration'):
                    self.summary_text.insert(tk.END, f"  Concentration: {group_info.get('concentration')}\n")
                self.summary_text.insert(tk.END, f"  Files: {len(group_info['files'])}\n")
                
                for j, file_info in enumerate(group_info['files'][:3]):
                    if isinstance(file_info, dict):
                        file_path = file_info.get('file_path', '')
                        sheet_info = f" [{file_info.get('sheet_name', '')}]" if file_info.get('sheet_name') else ""
                        meta_info = f" [Cell: {file_info.get('cell_id', '')}, {file_info.get('frequency', '')}Hz]"
                    else:
                        file_path = file_info
                        sheet_info = ""
                        meta_info = ""
                    self.summary_text.insert(tk.END, f"    • {Path(file_path).name}{sheet_info}{meta_info}\n")
                if len(group_info['files']) > 3:
                    self.summary_text.insert(tk.END, f"    ... and {len(group_info['files'])-3} more\n")
                
                self.summary_text.insert(tk.END, "\n")
        
        self.summary_text.config(state=tk.DISABLED)
    
    def stack_files(self):
        if not self.stack_groups:
            messagebox.showwarning("No Groups", "No groups defined. Please detect patterns or create manual groups.")
            return
        
        stacked_data = {}
        
        for group_name, group_info in self.stack_groups.items():
            try:
                all_traces = []
                time_data = None
                sweep_counter = 1
                
                files_list = sorted(group_info['files'], 
                                   key=lambda x: x.get('display_name', str(x)) if isinstance(x, dict) else str(x))
                
                for i, file_info in enumerate(files_list):
                    if isinstance(file_info, dict):
                        file_path = file_info['file_path']
                        sheet_name = file_info.get('sheet_name')
                        sweep_number_from_name = file_info.get('sweep_number', 0)
                        file_cell_id = file_info.get('cell_id', group_info.get('cell_id', 'Cell_Unknown'))
                        file_frequency = file_info.get('frequency', group_info.get('frequency', '1.0'))
                        file_drug = file_info.get('drug', group_info.get('drug', 'None'))
                        file_concentration = file_info.get('concentration', group_info.get('concentration', ''))
                    else:
                        file_path = file_info
                        sheet_name = None
                        sweep_number_from_name = 0
                        file_cell_id = group_info.get('cell_id', 'Cell_Unknown')
                        file_frequency = group_info.get('frequency', '1.0')
                        file_drug = group_info.get('drug', 'None')
                        file_concentration = group_info.get('concentration', '')
                    
                    path = Path(file_path)
                    
                    if path.suffix == '.abf':
                        messagebox.showwarning("ABF Files", 
                                              "ABF files cannot be directly stacked. Please use CSV/Excel files for stacking.")
                        continue
                    
                    try:
                        if path.suffix == '.csv':
                            # Try PatchMaster parser first
                            time_arr, volt_arr, pm_meta = parse_patchmaster_csv(file_path)
                            if time_arr is not None and volt_arr is not None:
                                df = pd.DataFrame({f'time': time_arr, 'voltage': volt_arr})
                                time_col, volt_col = 'time', 'voltage'
                            else:
                                df = pd.read_csv(file_path)
                                time_col, volt_col = fuzzy_find_columns(df)
                        else:
                            if sheet_name:
                                df = pd.read_excel(file_path, sheet_name=sheet_name)
                            else:
                                df = pd.read_excel(file_path)
                            time_col, volt_col = fuzzy_find_columns(df)
                    except Exception as e:
                        print(f"Error reading {file_path} sheet {sheet_name}: {e}")
                        continue
                    
                    if time_col is None or volt_col is None:
                        print(f"Could not find time/voltage columns in {file_path}")
                        continue
                    
                    # FIXED: Use the EXACT time array from the first file for all traces
                    # This ensures all traces have the same time base for stacking
                    if i == 0:
                        time_data = df[time_col].values
                    
                    trace_name = f"Trace_{i+1}"
                    
                    # Interpolate voltage data to match the common time base if necessary
                    current_time = df[time_col].values
                    current_voltage = df[volt_col].values
                    
                    if len(current_time) != len(time_data) or not np.allclose(current_time, time_data):
                        # Interpolate to common time base
                        voltage_data = np.interp(time_data, current_time, current_voltage)
                    else:
                        voltage_data = current_voltage
                    
                    import re
                    match = re.search(r'_(\d+)\.(?:xlsx|csv)$', path.name)
                    if match:
                        sweep_number = int(match.group(1))
                    elif sweep_number_from_name:
                        sweep_number = sweep_number_from_name
                    else:
                        sweep_number = sweep_counter
                        sweep_counter += 1
                    
                    all_traces.append({
                        'name': trace_name,
                        'data': voltage_data,
                        'file': path.name,
                        'sheet': sheet_name,
                        'index': i,
                        'sweep_number': sweep_number,
                        'cell_id': file_cell_id,
                        'frequency': file_frequency,
                        'drug': file_drug,
                        'concentration': file_concentration,
                        'condition': f"{file_drug} {file_concentration}".strip() if file_concentration else file_drug
                    })
                
                if time_data is not None and all_traces:
                    all_traces.sort(key=lambda x: x.get('sweep_number', 0))
                    
                    stacked_data[group_name] = {
                        'time': time_data,
                        'traces': all_traces,
                        'n_traces': len(all_traces),
                        'cell_id': group_info.get('cell_id', all_traces[0]['cell_id']),
                        'frequency': group_info.get('frequency', all_traces[0]['frequency']),
                        'drug': group_info.get('drug', all_traces[0]['drug']),
                        'concentration': group_info.get('concentration', ''),
                        'condition': group_info.get('condition', ''),
                        'stacked': True,
                        'group_name': group_name
                    }
                    
            except Exception as e:
                print(f"Error stacking group {group_name}: {e}")
                traceback.print_exc()
        
        if stacked_data:
            self.result = {
                "stacked_data": stacked_data,
                "grouping_info": {
                    "n_groups": len(stacked_data),
                    "method": "auto" if self.notebook.index("current") == 0 else "manual"
                }
            }
            
            summary_msg = f"Stacking Complete!\n\n"
            summary_msg += f"Successfully stacked {len(stacked_data)} groups:\n"
            for group_name, data in stacked_data.items():
                summary_msg += f"\n• {group_name}: {data['n_traces']} traces"
                summary_msg += f" (Cell: {data['cell_id']}, {data['frequency']} Hz"
                if data['drug'] and data['drug'] != 'None':
                    summary_msg += f", {data['drug']}"
                    if data['concentration']:
                        summary_msg += f" {data['concentration']}"
                summary_msg += ")"
            
            messagebox.showinfo("Stacking Complete", summary_msg)
            self.destroy()
        else:
            messagebox.showwarning("Stacking Failed", 
                                 "No valid files were stacked. Please check that you have selected CSV/Excel files.")
    
    def export_stacked(self):
        if not hasattr(self, 'result') or not self.result.get("stacked_data"):
            messagebox.showwarning("No Data", "No stacked data to export")
            return
        
        file_path = filedialog.asksaveasfilename(
            title="Save Stacked Excel File",
            defaultextension=".xlsx",
            filetypes=[("Excel files", "*.xlsx"), ("All files", "*.*")]
        )
        
        if not file_path:
            return
        
        try:
            with pd.ExcelWriter(file_path, engine='openpyxl') as writer:
                for group_name, data in self.result["stacked_data"].items():
                    time = data['time']
                    
                    df_dict = {'Time_ms': time}
                    for i, trace in enumerate(data['traces']):
                        df_dict[f'Trace_{i+1}'] = trace['data'][:len(time)]
                    
                    df = pd.DataFrame(df_dict)
                    # Sanitize sheet name for Excel
                    safe_sheet_name = sanitize_excel_sheet_name(group_name, 31)
                    df.to_excel(writer, sheet_name=safe_sheet_name, index=False)
                
                metadata = []
                for group_name, data in self.result["stacked_data"].items():
                    for i, trace in enumerate(data['traces']):
                        metadata.append({
                            'Group': group_name,
                            'Trace': f'Trace_{i+1}',
                            'Original_File': trace['file'],
                            'Sheet': trace.get('sheet', ''),
                            'Cell_ID': trace['cell_id'],
                            'Frequency_Hz': trace['frequency'],
                            'Drug': trace['drug'],
                            'Concentration': trace['concentration'],
                            'Condition': trace['condition'],
                            'Sweep_Number': trace.get('sweep_number', i+1)
                        })
                
                if metadata:
                    pd.DataFrame(metadata).to_excel(writer, sheet_name='Metadata', index=False)
                
                summary_data = []
                for group_name, data in self.result["stacked_data"].items():
                    summary_data.append({
                        'Stack_Name': group_name,
                        'Cell_ID': data['cell_id'],
                        'Frequency_Hz': data['frequency'],
                        'Drug': data['drug'],
                        'Concentration': data['concentration'],
                        'Number_of_Traces': data['n_traces'],
                        'Stacking_Method': self.result["grouping_info"]["method"]
                    })
                
                if summary_data:
                    pd.DataFrame(summary_data).to_excel(writer, sheet_name='Stack_Summary', index=False)
            
            messagebox.showinfo("Export Complete", f"Stacked data saved to:\n{file_path}")
            
        except Exception as e:
            messagebox.showerror("Export Error", f"Could not export stacked data: {str(e)}")
            traceback.print_exc()
    
    def cancel(self):
        self.result = None
        self.destroy()


# ============================================================================
# Enhanced Export System (FIXED for proper cell grouping in figures)
# ============================================================================

class EnhancedExportSystem:
    """Enhanced export system with organized folder structure and filename sanitization"""
    
    def __init__(self, output_folder, export_name, analysis_settings=None):
        self.output_folder = Path(output_folder) / export_name
        self.export_name = export_name
        self.export_summary = []
        self.one_figure_per_cell = False
        self.analysis_settings = analysis_settings
        
        self.output_folder.mkdir(parents=True, exist_ok=True)
    
    def sanitize_filename(self, filename, max_length=200):
        """
        Sanitize filename by removing/replacing invalid characters.
        Prevents OSError when creating files with newlines or special characters.
        """
        return sanitize_filename(filename, max_length)
    
    def sanitize_excel_sheet_name(self, sheet_name):
        """Sanitize Excel sheet name according to Excel limitations"""
        return sanitize_excel_sheet_name(sheet_name, 31)
    
    def all_results_for_group(self, condition_key, all_results):
        group_results = []
        for res in all_results:
            res_condition = f"{res.get('cell_id', 'unknown')}_{res.get('frequency', 'unknown')}Hz"
            if res.get('drug') and res.get('drug') != 'None':
                res_condition += f"_{res.get('drug')}"
                if res.get('concentration'):
                    res_condition += f"_{res.get('concentration')}"
            if res.get('range_name'):
                res_condition += f"_{res.get('range_name')}"
            
            if res_condition == condition_key:
                group_results.append(res)
        return group_results
    
    def set_one_figure_per_cell(self, value):
        self.one_figure_per_cell = value
    
    def create_export_summary(self):
        """Create detailed export summary with processing information"""
        summary_path = self.output_folder / "Export_Summary.txt"
        with open(summary_path, 'w') as f:
            f.write("=" * 70 + "\n")
            f.write("APEX EXPORT SUMMARY\n")
            f.write("=" * 70 + "\n\n")
        
            f.write(f"Export Name: {self.export_name}\n")
            f.write(f"Export Date: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"Export Location: {self.output_folder}\n\n")
        
            f.write("-" * 70 + "\n")
            f.write("PROCESSING INFORMATION\n")
            f.write("-" * 70 + "\n\n")
        
            if self.analysis_settings:
                f.write("Analysis Settings:\n")
                f.write(f"  • Species: {self.analysis_settings.get('species', 'auto')}\n")
                f.write(f"  • Cardioid Immature Mode: {self.analysis_settings.get('immature_mode', False)}\n")
                f.write(f"  • Smoothing Enabled: {self.analysis_settings.get('smoothing_enabled', True)}\n")
                f.write(f"  • Smoothing Method: {self.analysis_settings.get('smooth_method', 'savgol')}\n")
                f.write(f"  • Smoothing Window: {self.analysis_settings.get('smoothing_ms', 'adaptive')} ms\n")
                f.write(f"  • Dual-path Detection: {self.analysis_settings.get('dual_path', True)}\n")
                f.write(f"  • Corrected APD80/90: {self.analysis_settings.get('corrected_apd', True)}\n\n")
            
                f.write("dV/dt_max Calculation:\n")
                f.write("  • Method: Dual-path with minimal smoothing (0.5 ms) on upstroke region\n")
                f.write("  • Global smoothing affects visualization only, not dV/dt_max\n")
                f.write("  • Upstroke detection uses minimally-smoothed trace for accuracy\n\n")
            else:
                f.write("Note: Detailed analysis settings not available in this export.\n\n")
        
            f.write("-" * 70 + "\n")
            f.write("FILES CREATED\n")
            f.write("-" * 70 + "\n")
            for item in self.export_summary:
                f.write(f"  • {item}\n")
        
            f.write("\n" + "-" * 70 + "\n")
            f.write("LEGEND & NOTES\n")
            f.write("-" * 70 + "\n\n")
            f.write("Correction Types:\n")
            f.write("  • Auto: Automatically detected peak and upstroke\n")
            f.write("  • Peak: Manually corrected peak position\n")
            f.write("  • Upstroke: Manually corrected upstroke start for accurate dV/dt_max\n")
            f.write("  • LateRepol: Late repolarization correction (APD50-APD70 linear fit)\n")
            f.write("  • Combined: Multiple corrections applied (e.g., Peak+Upstroke)\n\n")
        
            f.write("APD Measurements:\n")
            f.write("  • APD80/90: Standard repolarization levels (80% and 90% repolarization)\n")
            f.write("  • Corrected APD80/90: Linear fit using APD50-APD70 for bump detection\n")
            f.write("  • Raw APD80/90: Original values before correction (if applicable)\n\n")
        
            f.write("Quality Metrics:\n")
            f.write("  • Upstroke Quality Score: 0-1 confidence in upstroke detection\n")
            f.write("  • STV (Short-Term Variability): Beat-to-beat APD variability\n")
            f.write("  • Repolarization Fraction: (APD90-APD50)/APD90\n\n")
        
            f.write("Export Structure:\n")
            f.write("  • Data/ - Excel files with AP parameters and statistics\n")
            f.write("  • Traces/ - Individual and average trace CSV files\n")
            f.write("  • Figures/ - Publication-quality figures\n")
        
            f.write("\n" + "=" * 70 + "\n")
            f.write("END OF EXPORT SUMMARY\n")
            f.write("=" * 70 + "\n")
    
    def add_to_summary(self, item):
            self.export_summary.append(item)
    
    def export_selected_results(self, selected_results, export_options=None):
        if not selected_results:
            return None
        
        data_folder = self.output_folder / "Data"
        data_folder.mkdir(exist_ok=True)
        
        export_individual = export_options and export_options.get('individual_traces', True)
        export_average = export_options and export_options.get('average_traces', True)
        
        if export_individual or export_average:
            traces_folder = self.output_folder / "Traces"
            traces_folder.mkdir(exist_ok=True)
            
            individual_traces_folder = traces_folder / "Individual_Traces"
            average_traces_folder = traces_folder / "Average_Traces"
            
            if export_individual:
                individual_traces_folder.mkdir(exist_ok=True)
            if export_average:
                average_traces_folder.mkdir(exist_ok=True)
        else:
            individual_traces_folder = None
            average_traces_folder = None
        
        if export_options and export_options.get('ap_parameter_matrix', True):
            self.export_ap_parameter_matrix(selected_results, data_folder / "AP_Parameter_Matrix.xlsx")
        
        if export_options and export_options.get('raw_ap_data', True):
            self.export_raw_ap_data_table(selected_results, data_folder / "RAW_AP_Data.xlsx")
        
        if export_options and export_options.get('frequency_drug_response', True):
            self.export_frequency_drug_response(selected_results, data_folder / "Frequency_Drug_Response.xlsx")
        
        if export_options and export_options.get('comprehensive_analysis', True):
            self.export_comprehensive_excel(selected_results, data_folder / "Comprehensive_Analysis.xlsx")
        
        if export_individual and individual_traces_folder:
            self.export_individual_traces_csv(selected_results, individual_traces_folder)
        
        if export_average and average_traces_folder:
            self.export_average_traces_csv(selected_results, average_traces_folder)
        
        if export_options and export_options.get('figures'):
            figures_folder = self.output_folder / "Figures"
            figures_folder.mkdir(exist_ok=True)
            self.export_enhanced_figures(selected_results, figures_folder, export_options['figure_types'])
        
        self.create_export_summary()
        return self.output_folder
    
    def export_ap_parameter_matrix(self, results, filepath):

        all_params_data = []
        groups = defaultdict(lambda: defaultdict(list))
        
        for res in results:
            cell_id = res.get('cell_id', 'unknown')
            frequency = res.get('frequency', 'unknown')
            drug = res.get('drug', 'None')
            concentration = res.get('concentration', '')
            range_name = res.get('range_name', '')
            
            condition_key = f"{cell_id}_{frequency}Hz"
            if drug and drug != 'None':
                condition_key += f"_{drug}"
                if concentration:
                    condition_key += f"_{concentration}"
            if range_name:
                condition_key += f"_{range_name}"
            
            ap_counter = 0
            for ap in res.get('ap_metrics', []):
                ap_counter += 1
                
                correction_parts = []
                if ap.get('has_manual_correction', False):
                    correction_parts.append('Peak')
                if ap.get('has_manual_upstroke', False):
                    correction_parts.append('Upstroke')
                if ap.get('has_late_repol', False):
                    correction_parts.append('LateRepol')
                
                correction_display = '+'.join(correction_parts) if correction_parts else 'Auto'
                
                param_row = {
                    'Condition': condition_key,
                    'Cell_ID': cell_id,
                    'Frequency_Hz': frequency,
                    'Drug': drug,
                    'Concentration': concentration,
                    'Range': range_name,
                    'Trace_ID': self.get_safe_trace_id(res),
                    'AP_Index': ap_counter,
                    'RMP_mV': ap.get('RMP', np.nan),
                    'RMP_Method': ap.get('RMP_method', ''),
                    'APA_mV': ap.get('APA', np.nan),
                    'dVdt_max_mVms': ap.get('dVdt_max', np.nan),
                    'Overshoot_mV': ap.get('Overshoot', np.nan),
                    'dVdt_max_physiological': ap.get('dVdt_max_physiological', False),
                    'Has_Bump': ap.get('has_bump', False),
                    'Late_Repolarization_Corrected': ap.get('late_repolarization_corrected', False),
                    'Upstroke_Manual': ap.get('upstroke_manual', False),
                    'Repolarization_Fraction': ap.get('Repolarization_Fraction', np.nan),
                    'Use_Corrected_APD': ap.get('use_corrected_apd', True),
                    'Correction_Type': correction_display,
                    'Adaptive_Smoothing_Used': res.get('adaptive_smoothing_used', False),
                    'Smoothing_Used_ms': res.get('smoothing_ms_used', np.nan),
                    'Sampling_Rate_Hz': res.get('sampling_rate_hz', np.nan)
                }
                
                # Add upstroke quality metrics if available
                if 'upstroke_quality_score' in ap:
                    param_row['Upstroke_Quality_Score'] = ap.get('upstroke_quality_score', np.nan)
                    param_row['Upstroke_Quality'] = ap.get('upstroke_quality', 'N/A')
                    param_row['Upstroke_SNR'] = ap.get('upstroke_snr', np.nan)
                
                # Add raw APD80/APD90 if late repolarization correction was applied
                if ap.get('late_repolarization_corrected', False):
                    # Store raw values (pre-correction) in dedicated columns
                    param_row['APD80_raw_ms'] = ap.get('APD80_raw', np.nan)
                    param_row['APD90_raw_ms'] = ap.get('APD90_raw', np.nan)
                    # Store corrected values in standard columns
                    param_row['APD80_corrected_ms'] = ap.get('APD80', np.nan)
                    param_row['APD90_corrected_ms'] = ap.get('APD90', np.nan)
                else:
                    # No correction applied: raw = corrected
                    param_row['APD80_raw_ms'] = ap.get('APD80', np.nan)
                    param_row['APD90_raw_ms'] = ap.get('APD90', np.nan)
                    param_row['APD80_corrected_ms'] = ap.get('APD80', np.nan)
                    param_row['APD90_corrected_ms'] = ap.get('APD90', np.nan)
                
                # Standard APD columns (all percentages)
                for percent in APD_PERCENTAGES:
                    if percent == 80:
                        param_row[f'APD{percent}_ms'] = param_row['APD80_corrected_ms']
                    elif percent == 90:
                        param_row[f'APD{percent}_ms'] = param_row['APD90_corrected_ms']
                    else:
                        param_row[f'APD{percent}_ms'] = ap.get(f'APD{percent}', np.nan)
                
                groups[condition_key]['APD90'].append(ap.get('APD90', np.nan))
                groups[condition_key]['APA'].append(ap.get('APA', np.nan))
                groups[condition_key]['RMP'].append(ap.get('RMP', np.nan))
                groups[condition_key]['dVdt_max'].append(ap.get('dVdt_max', np.nan))
                groups[condition_key]['Repolarization_Fraction'].append(ap.get('Repolarization_Fraction', np.nan))
                
                for percent in APD_PERCENTAGES:
                    apd_key = f'APD{percent}'
                    if apd_key not in groups[condition_key]:
                        groups[condition_key][apd_key] = []
                    groups[condition_key][apd_key].append(ap.get(f'APD{percent}', np.nan))
                
                all_params_data.append(param_row)
        
        if all_params_data:
            df_all = pd.DataFrame(all_params_data)
            
            with pd.ExcelWriter(filepath, engine='openpyxl') as writer:
                df_all.to_excel(writer, sheet_name='All_AP_Parameters', index=False)
                
                # Split Parameter_Averages into three sheets
                avg_rows_raw, avg_rows_corrected, avg_rows_combined = self.create_parameter_averages_sheets(groups, df_all.columns, results)
                
                if avg_rows_raw:
                    df_avg_raw = pd.DataFrame(avg_rows_raw)
                    df_avg_raw.to_excel(writer, sheet_name='Parameter_Averages_Raw', index=False)
                
                if avg_rows_corrected:
                    df_avg_corrected = pd.DataFrame(avg_rows_corrected)
                    df_avg_corrected.to_excel(writer, sheet_name='Parameter_Averages_Corrected', index=False)
                
                if avg_rows_combined:
                    df_avg_combined = pd.DataFrame(avg_rows_combined)
                    df_avg_combined.to_excel(writer, sheet_name='Parameter_Averages', index=False)
                
                self.create_summary_statistics_sheet(results, writer)
            
            self.add_to_summary(f"AP Parameter Matrix (5 sheets): {filepath.name}")
    
    def create_parameter_averages_sheets(self, groups, all_columns, all_results):
        """Create three separate averages sheets: Raw, Corrected, and Combined"""
        avg_rows_raw = []
        avg_rows_corrected = []
        avg_rows_combined = []
        
        condition_groups = defaultdict(lambda: {
            'ap_metrics': [],
            'sweep_numbers': set(),
            'filenames': set(),
            'correction_counts': {'peak': 0, 'upstroke': 0, 'late_repol': 0},
            'cell_id': None,
            'frequency': None,
            'drug': None,
            'concentration': None
        })
    
        # FIRST PASS: Group by Cell_ID + Frequency (ignore sweep number/trace number)
        for res in all_results:
            cell_id = res.get('cell_id', 'unknown')
            frequency = res.get('frequency', 'unknown')
            drug = res.get('drug', 'None')
            concentration = res.get('concentration', '')
            range_name = res.get('range_name', '')
        
            # Create group key by CELL ID + FREQUENCY (NOT by individual file)
            group_key = f"{cell_id}_{frequency}Hz"
        
            # Add drug info if present (for drug studies)
            if drug and drug != 'None':
                group_key += f"_{drug}"
                if concentration:
                    group_key += f"_{concentration}"
        
            # Initialize group data if not exists
            group_data = condition_groups[group_key]
            group_data['cell_id'] = cell_id
            group_data['frequency'] = frequency
            group_data['drug'] = drug
            group_data['concentration'] = concentration
        
            # Store all AP metrics for this cell+frequency combination
            for ap in res.get('ap_metrics', []):
                group_data['ap_metrics'].append(ap)
            
                # Count corrections
                if ap.get('has_manual_correction', False):
                    group_data['correction_counts']['peak'] += 1
                if ap.get('has_manual_upstroke', False):
                    group_data['correction_counts']['upstroke'] += 1
                if ap.get('has_late_repol', False):
                    group_data['correction_counts']['late_repol'] += 1
        
            # Track which files/sweeps contributed to this group
            sweep_number = 0
            if res.get('file_type') == 'CSV/Excel' and range_name:
                import re
                match = re.search(r'_(\d+)\.(?:xlsx|csv)$', range_name)
                if match:
                    sweep_number = int(match.group(1))
            else:
                sweep_number = res.get('sweep_number', 0)
        
            if sweep_number > 0:
                group_data['sweep_numbers'].add(sweep_number)
            group_data['filenames'].add(res.get('file_name', ''))
    
        # SECOND PASS: Create average rows for each cell+frequency group
        for group_key, group_data in condition_groups.items():
            if not group_data.get('ap_metrics'):
                continue
        
            n_aps = len(group_data['ap_metrics'])
            cell_id = group_data['cell_id']
            frequency = group_data['frequency']
        
            # Create display name for the average row
            base_row = {
                'Condition': group_key,
                'Cell_ID': cell_id,
                'Frequency_Hz': frequency,
                'Drug': group_data.get('drug', 'None'),
                'Concentration': group_data.get('concentration', ''),
                'Range': f"AVG_{cell_id}_{frequency}Hz",
                'Trace_ID': f"AVG_{cell_id}_{frequency}Hz",
                'AP_Index': f"n={n_aps}",
                'n_Peak_Corrections': group_data['correction_counts'].get('peak', 0),
                'n_Upstroke_Corrections': group_data['correction_counts'].get('upstroke', 0),
                'n_Late_Repolarization_Corrections': group_data['correction_counts'].get('late_repol', 0),
                'n_Late_Repolarization_Corrected_APs': sum(1 for ap in group_data['ap_metrics'] if ap.get('late_repolarization_corrected', False))
            }
        
            # Calculate averages for each parameter
            param_sums = defaultdict(list)
            raw_apd80_sums = []
            raw_apd90_sums = []
            corrected_apd80_sums = []
            corrected_apd90_sums = []
        
            for ap in group_data['ap_metrics']:
                # Basic parameters
                for param_key, excel_col in [
                    ('RMP', 'RMP_mV'),
                    ('APA', 'APA_mV'),
                    ('dVdt_max', 'dVdt_max_mVms'),
                    ('Overshoot', 'Overshoot_mV'),
                    ('Repolarization_Fraction', 'Repolarization_Fraction')
                ]:
                    val = ap.get(param_key)
                    if val is not None and not math.isnan(val):
                        param_sums[excel_col].append(val)

                # Handle raw vs corrected APD80/APD90
                if ap.get('late_repolarization_corrected', False):
                    # Use raw values if available
                    raw_val_80 = ap.get('APD80_raw', ap.get('APD80', np.nan))
                    raw_val_90 = ap.get('APD90_raw', ap.get('APD90', np.nan))
                    corrected_val_80 = ap.get('APD80', np.nan)
                    corrected_val_90 = ap.get('APD90', np.nan)
                else:
                    # No correction: raw = corrected
                    raw_val_80 = ap.get('APD80', np.nan)
                    raw_val_90 = ap.get('APD90', np.nan)
                    corrected_val_80 = ap.get('APD80', np.nan)
                    corrected_val_90 = ap.get('APD90', np.nan)
                
                if not math.isnan(raw_val_80):
                    raw_apd80_sums.append(raw_val_80)
                if not math.isnan(raw_val_90):
                    raw_apd90_sums.append(raw_val_90)
                if not math.isnan(corrected_val_80):
                    corrected_apd80_sums.append(corrected_val_80)
                if not math.isnan(corrected_val_90):
                    corrected_apd90_sums.append(corrected_val_90)

                # APD percentages
                for percent in APD_PERCENTAGES:
                    if percent in [80, 90]:
                        continue
                    val = ap.get(f'APD{percent}')
                    if val is not None and not math.isnan(val):
                        param_sums[f'APD{percent}_ms'].append(val)
        
            # Add raw and corrected APD80/APD90 to param_sums
            if raw_apd80_sums:
                param_sums['APD80_raw_ms'] = raw_apd80_sums
            if raw_apd90_sums:
                param_sums['APD90_raw_ms'] = raw_apd90_sums
            if corrected_apd80_sums:
                param_sums['APD80_corrected_ms'] = corrected_apd80_sums
            if corrected_apd90_sums:
                param_sums['APD90_corrected_ms'] = corrected_apd90_sums
        
            # Calculate means for each parameter
            for excel_col, values in param_sums.items():
                if values:
                    base_row[excel_col] = np.nanmean(values)
                else:
                    base_row[excel_col] = np.nan
        
            # Calculate STV for this group
            all_apd90 = [ap.get('APD90', np.nan) for ap in group_data['ap_metrics'] 
                        if not math.isnan(ap.get('APD90', np.nan))]
        
            if len(all_apd90) >= 5:
                stv_val, stv_note = calculate_stv(all_apd90)
                base_row['STV_APD90'] = stv_val
                base_row['STV_Note'] = stv_note
            else:
                base_row['STV_APD90'] = np.nan
                base_row['STV_Note'] = f"Insufficient beats: {len(all_apd90)}"
        
            # Create Raw sheet row (excludes corrected columns)
            raw_row = base_row.copy()
            raw_row.pop('APD80_corrected_ms', None)
            raw_row.pop('APD90_corrected_ms', None)
            avg_rows_raw.append(raw_row)
        
            # Create Corrected sheet row (excludes raw columns)
            corrected_row = base_row.copy()
            corrected_row.pop('APD80_raw_ms', None)
            corrected_row.pop('APD90_raw_ms', None)
            avg_rows_corrected.append(corrected_row)
        
            # Create Combined sheet row (has both)
            avg_rows_combined.append(base_row.copy())
    
        # Sort by Cell ID and then by frequency
        def sort_key(row):
            freq_str = row.get('Frequency_Hz', '0')
            try:
                freq_num = float(freq_str)
            except:
                freq_num = 0
            return (row.get('Cell_ID', ''), freq_num)
    
        avg_rows_raw.sort(key=sort_key)
        avg_rows_corrected.sort(key=sort_key)
        avg_rows_combined.sort(key=sort_key)
    
        return avg_rows_raw, avg_rows_corrected, avg_rows_combined
    
    def create_summary_statistics_sheet(self, results, writer):
        groups = defaultdict(lambda: defaultdict(list))
        
        for res in results:
            key = f"{res.get('cell_id')}_{res.get('frequency')}Hz"
            if res.get('drug') and res.get('drug') != 'None':
                key += f"_{res.get('drug')}"
                if res.get('concentration'):
                    key += f"_{res.get('concentration')}"
            
            for ap in res.get('ap_metrics', []):
                groups[key]['APD90'].append(ap.get('APD90', np.nan))
                groups[key]['APA'].append(ap.get('APA', np.nan))
                groups[key]['RMP'].append(ap.get('RMP', np.nan))
                groups[key]['dVdt_max'].append(ap.get('dVdt_max', np.nan))
                groups[key]['Repolarization_Fraction'].append(ap.get('Repolarization_Fraction', np.nan))
        
        summary_rows = []
        
        for condition, params in groups.items():
            apd90_vals = [v for v in params['APD90'] if not math.isnan(v)]
            if apd90_vals:
                summary_rows.append({
                    'Condition': condition,
                    'Parameter': 'APD90',
                    'n': len(apd90_vals),
                    'Mean_ms': np.mean(apd90_vals),
                    'SEM_ms': np.std(apd90_vals) / np.sqrt(len(apd90_vals)) if len(apd90_vals) > 1 else 0,
                    'SD_ms': np.std(apd90_vals) if len(apd90_vals) > 1 else 0,
                    'Min_ms': np.min(apd90_vals) if apd90_vals else np.nan,
                    'Max_ms': np.max(apd90_vals) if apd90_vals else np.nan,
                    'CV_%': (np.std(apd90_vals) / np.mean(apd90_vals) * 100) if len(apd90_vals) > 1 and np.mean(apd90_vals) != 0 else np.nan
                })
            
            apa_vals = [v for v in params['APA'] if not math.isnan(v)]
            if apa_vals:
                summary_rows.append({
                    'Condition': condition,
                    'Parameter': 'APA',
                    'n': len(apa_vals),
                    'Mean_mV': np.mean(apa_vals),
                    'SEM_mV': np.std(apa_vals) / np.sqrt(len(apa_vals)) if len(apa_vals) > 1 else 0,
                    'SD_mV': np.std(apa_vals) if len(apa_vals) > 1 else 0,
                    'Min_mV': np.min(apa_vals) if apa_vals else np.nan,
                    'Max_mV': np.max(apa_vals) if apa_vals else np.nan,
                    'CV_%': (np.std(apa_vals) / np.mean(apa_vals) * 100) if len(apa_vals) > 1 and np.mean(apa_vals) != 0 else np.nan
                })
            
            rmp_vals = [v for v in params['RMP'] if not math.isnan(v)]
            if rmp_vals:
                summary_rows.append({
                    'Condition': condition,
                    'Parameter': 'RMP',
                    'n': len(rmp_vals),
                    'Mean_mV': np.mean(rmp_vals),
                    'SEM_mV': np.std(rmp_vals) / np.sqrt(len(rmp_vals)) if len(rmp_vals) > 1 else 0,
                    'SD_mV': np.std(rmp_vals) if len(rmp_vals) > 1 else 0,
                    'Min_mV': np.min(rmp_vals) if rmp_vals else np.nan,
                    'Max_mV': np.max(rmp_vals) if rmp_vals else np.nan,
                    'CV_%': (np.std(rmp_vals) / np.mean(rmp_vals) * 100) if len(rmp_vals) > 1 and np.mean(rmp_vals) != 0 else np.nan
                })
            
            dvdt_vals = [v for v in params['dVdt_max'] if not math.isnan(v)]
            if dvdt_vals:
                summary_rows.append({
                    'Condition': condition,
                    'Parameter': 'dV/dt_max',
                    'n': len(dvdt_vals),
                    'Mean_mVms': np.mean(dvdt_vals),
                    'SEM_mVms': np.std(dvdt_vals) / np.sqrt(len(dvdt_vals)) if len(dvdt_vals) > 1 else 0,
                    'SD_mVms': np.std(dvdt_vals) if len(dvdt_vals) > 1 else 0,
                    'Min_mVms': np.min(dvdt_vals) if dvdt_vals else np.nan,
                    'Max_mVms': np.max(dvdt_vals) if dvdt_vals else np.nan,
                    'CV_%': (np.std(dvdt_vals) / np.mean(dvdt_vals) * 100) if len(dvdt_vals) > 1 and np.mean(dvdt_vals) != 0 else np.nan
                })
            
            repol_vals = [v for v in params['Repolarization_Fraction'] if not math.isnan(v)]
            if repol_vals:
                summary_rows.append({
                    'Condition': condition,
                    'Parameter': 'Repolarization_Fraction',
                    'n': len(repol_vals),
                    'Mean': np.mean(repol_vals),
                    'SEM': np.std(repol_vals) / np.sqrt(len(repol_vals)) if len(repol_vals) > 1 else 0,
                    'SD': np.std(repol_vals) if len(repol_vals) > 1 else 0,
                    'Min': np.min(repol_vals) if repol_vals else np.nan,
                    'Max': np.max(repol_vals) if repol_vals else np.nan,
                    'CV_%': (np.std(repol_vals) / np.mean(repol_vals) * 100) if len(repol_vals) > 1 and np.mean(repol_vals) != 0 else np.nan
                })
        
        if summary_rows:
            pd.DataFrame(summary_rows).to_excel(writer, sheet_name='Summary_Statistics', index=False)
    
    def export_comprehensive_excel(self, results, filepath):
        with pd.ExcelWriter(filepath, engine='openpyxl') as writer:
            all_params = []
            for res in results:
                apd_values = [ap.get('APD90', np.nan) for ap in res.get('ap_metrics', [])]
                apd_values = [v for v in apd_values if not math.isnan(v)]
                stv_val = np.nan
                stv_note = ""
                
                if len(apd_values) >= 5:
                    stv_val, stv_note = calculate_stv(apd_values)
                
                for ap in res.get('ap_metrics', []):
                    correction_parts = []
                    if ap.get('has_manual_correction', False):
                        correction_parts.append('Peak')
                    if ap.get('has_manual_upstroke', False):
                        correction_parts.append('Upstroke')
                    if ap.get('has_late_repol', False):
                        correction_parts.append('LateRepol')
                    
                    correction_display = '+'.join(correction_parts) if correction_parts else 'Auto'
                    
                    param_row = {
                        'Trace_ID': self.get_safe_trace_id(res),
                        'File': res.get('file_name', ''),
                        'Cell_ID': res.get('cell_id', ''),
                        'Frequency_Hz': res.get('frequency', ''),
                        'Drug': res.get('drug', ''),
                        'Concentration': res.get('concentration', ''),
                        'Species': res.get('species', ''),
                        'Correction_Type': correction_display,
                        'Peak_Time_ms': ap.get('peak_time', np.nan),
                        'RMP_mV': ap.get('RMP', np.nan),
                        'RMP_Method': ap.get('RMP_method', ''),
                        'APA_mV': ap.get('APA', np.nan),
                        'dVdt_max_mVms': ap.get('dVdt_max', np.nan),
                        'Overshoot_mV': ap.get('Overshoot', np.nan),
                        'STV_APD90': stv_val,
                        'STV_Note': stv_note,
                        'Has_Bump': ap.get('has_bump', False),
                        'Late_Repolarization_Corrected': ap.get('late_repolarization_corrected', False),
                        'Upstroke_Manual': ap.get('upstroke_manual', False),
                        'Repolarization_Fraction': ap.get('Repolarization_Fraction', np.nan),
                        'Adaptive_Smoothing_Used': res.get('adaptive_smoothing_used', False),
                        'Smoothing_Used_ms': res.get('smoothing_ms_used', np.nan),
                        'Sampling_Rate_Hz': res.get('sampling_rate_hz', np.nan)
                    }
                    
                    # Add upstroke quality metrics if available
                    if 'upstroke_quality_score' in ap:
                        param_row['Upstroke_Quality_Score'] = ap.get('upstroke_quality_score', np.nan)
                        param_row['Upstroke_Quality'] = ap.get('upstroke_quality', 'N/A')
                    
                    # Add raw APD80/APD90 if late repolarization correction was applied
                    if ap.get('late_repolarization_corrected', False):
                        param_row['APD80_raw_ms'] = ap.get('APD80_raw', np.nan)
                        param_row['APD90_raw_ms'] = ap.get('APD90_raw', np.nan)
                        param_row['APD80_corrected_ms'] = ap.get('APD80', np.nan)
                        param_row['APD90_corrected_ms'] = ap.get('APD90', np.nan)
                    else:
                        param_row['APD80_raw_ms'] = ap.get('APD80', np.nan)
                        param_row['APD90_raw_ms'] = ap.get('APD90', np.nan)
                        param_row['APD80_corrected_ms'] = ap.get('APD80', np.nan)
                        param_row['APD90_corrected_ms'] = ap.get('APD90', np.nan)
                    
                    for percent in APD_PERCENTAGES:
                        # Skip APD95 as requested by user
                        if percent == 95:
                            continue
                        param_row[f'APD{percent}_ms'] = ap.get(f'APD{percent}', np.nan)
                    
                    all_params.append(param_row)
            
            if all_params:
                pd.DataFrame(all_params).to_excel(writer, sheet_name='All_AP_Parameters', index=False)
            
            self.create_stv_detailed_sheet(results, writer)
            self.create_frequency_drug_analysis_sheet_with_stv(results, writer)
        
        self.add_to_summary(f"Comprehensive Analysis: {filepath.name}")
    
    def create_frequency_drug_analysis_sheet_with_stv(self, results, writer):
        analysis_rows = []
        cells = defaultdict(list)
        
        for res in results:
            cell_id = res.get('cell_id', '')
            cells[cell_id].append(res)
        
        for cell_id, cell_results in cells.items():
            freq_drug_data = defaultdict(lambda: defaultdict(list))
            for res in cell_results:
                freq = res.get('frequency', '')
                drug = res.get('drug', 'None')
                
                for ap in res.get('ap_metrics', []):
                    freq_drug_data[freq][drug].append({
                        'APD90': ap.get('APD90', np.nan),
                        'APA': ap.get('APA', np.nan),
                        'RMP': ap.get('RMP', np.nan),
                        'dVdt_max': ap.get('dVdt_max', np.nan),
                        'Overshoot': ap.get('Overshoot', np.nan),
                        'Repolarization_Fraction': ap.get('Repolarization_Fraction', np.nan)
                    })
            
            for freq, drug_data in freq_drug_data.items():
                for drug, ap_values in drug_data.items():
                    if ap_values:
                        apd90_values = [v['APD90'] for v in ap_values if not math.isnan(v['APD90'])]
                        apa_values = [v['APA'] for v in ap_values if not math.isnan(v['APA'])]
                        rmp_values = [v['RMP'] for v in ap_values if not math.isnan(v['RMP'])]
                        dvdt_values = [v['dVdt_max'] for v in ap_values if not math.isnan(v['dVdt_max'])]
                        overshoot_values = [v['Overshoot'] for v in ap_values if not math.isnan(v['Overshoot'])]
                        repol_values = [v['Repolarization_Fraction'] for v in ap_values if not math.isnan(v['Repolarization_Fraction'])]
                        
                        stv_val = np.nan
                        stv_note = ""
                        if len(apd90_values) >= 5:
                            stv_val, stv_note = calculate_stv(apd90_values)
                        
                        analysis_rows.append({
                            'Cell_ID': cell_id,
                            'Frequency_Hz': freq,
                            'Drug': drug,
                            'n': len(ap_values),
                            'APD90_mean_ms': np.mean(apd90_values) if apd90_values else np.nan,
                            'APD90_SEM_ms': np.std(apd90_values) / np.sqrt(len(apd90_values)) if len(apd90_values) > 1 else 0,
                            'APA_mean_mV': np.mean(apa_values) if apa_values else np.nan,
                            'APA_SEM_mV': np.std(apa_values) / np.sqrt(len(apa_values)) if apa_values and len(apa_values) > 1 else 0,
                            'RMP_mean_mV': np.mean(rmp_values) if rmp_values else np.nan,
                            'RMP_SEM_mV': np.std(rmp_values) / np.sqrt(len(rmp_values)) if rmp_values and len(rmp_values) > 1 else 0,
                            'dVdt_max_mean_mVms': np.mean(dvdt_values) if dvdt_values else np.nan,
                            'dVdt_max_SEM_mVms': np.std(dvdt_values) / np.sqrt(len(dvdt_values)) if dvdt_values and len(dvdt_values) > 1 else 0,
                            'Overshoot_mean_mV': np.mean(overshoot_values) if overshoot_values else np.nan,
                            'Overshoot_SEM_mV': np.std(overshoot_values) / np.sqrt(len(overshoot_values)) if overshoot_values and len(overshoot_values) > 1 else 0,
                            'Repolarization_Fraction_mean': np.mean(repol_values) if repol_values else np.nan,
                            'Repolarization_Fraction_SEM': np.std(repol_values) / np.sqrt(len(repol_values)) if repol_values and len(repol_values) > 1 else 0,
                            'STV_APD90': stv_val,
                            'STV_Note': stv_note
                        })
        
        if analysis_rows:
            pd.DataFrame(analysis_rows).to_excel(writer, sheet_name='Frequency_Drug_Analysis', index=False)
    
    def create_stv_detailed_sheet(self, results, writer):
        stv_rows = []
        
        for res in results:
            apd_values = [ap.get('APD90', np.nan) for ap in res.get('ap_metrics', [])]
            apd_values = [v for v in apd_values if not math.isnan(v)]
            
            if len(apd_values) >= 5:
                stv_val, stv_note = calculate_stv(apd_values)
                
                apd_n = apd_values[:-1]
                apd_n1 = apd_values[1:]
                differences = np.array(apd_n1) - np.array(apd_n)
                sd1 = np.std(differences) / np.sqrt(2) if len(differences) > 1 else 0
                sums = [apd_n[i] + apd_n1[i] for i in range(len(apd_n))]
                sd2 = np.std(sums) / np.sqrt(2) if len(sums) > 1 else 0
                
                stv_rows.append({
                    'Trace_ID': self.get_safe_trace_id(res),
                    'File': res.get('file_name', ''),
                    'Cell_ID': res.get('cell_id', ''),
                    'Frequency_Hz': res.get('frequency', ''),
                    'Drug': res.get('drug', ''),
                    'n_beats': len(apd_values),
                    'APD90_mean_ms': np.mean(apd_values),
                    'APD90_SD_ms': np.std(apd_values) if len(apd_values) > 1 else 0,
                    'APD90_CV_%': (np.std(apd_values) / np.mean(apd_values) * 100) if len(apd_values) > 1 and np.mean(apd_values) != 0 else np.nan,
                    'STV_APD90': stv_val,
                    'SD1_ms': sd1,
                    'SD2_ms': sd2,
                    'SD1_SD2_ratio': sd1 / sd2 if sd2 != 0 else np.nan,
                    'STV_Note': stv_note
                })
            else:
                stv_rows.append({
                    'Trace_ID': self.get_safe_trace_id(res),
                    'File': res.get('file_name', ''),
                    'Cell_ID': res.get('cell_id', ''),
                    'Frequency_Hz': res.get('frequency', ''),
                    'Drug': res.get('drug', ''),
                    'n_beats': len(apd_values),
                    'APD90_mean_ms': np.mean(apd_values) if apd_values else np.nan,
                    'APD90_SD_ms': np.std(apd_values) if len(apd_values) > 1 else 0,
                    'APD90_CV_%': (np.std(apd_values) / np.mean(apd_values) * 100) if len(apd_values) > 1 and np.mean(apd_values) != 0 else np.nan,
                    'STV_APD90': np.nan,
                    'SD1_ms': np.nan,
                    'SD2_ms': np.nan,
                    'SD1_SD2_ratio': np.nan,
                    'STV_Note': f"Insufficient beats: {len(apd_values)}"
                })
        
        if stv_rows:
            pd.DataFrame(stv_rows).to_excel(writer, sheet_name='STV_Detailed_Analysis', index=False)
    
    def export_frequency_drug_response(self, results, filepath):
        analysis_data = []
        cells = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))
        
        for res in results:
            cell_id = res.get('cell_id', 'unknown')
            frequency = res.get('frequency', 'unknown')
            drug = res.get('drug', 'None')
            
            for ap in res.get('ap_metrics', []):
                cells[cell_id][frequency][drug].append({
                    'APD90': ap.get('APD90', np.nan),
                    'APA': ap.get('APA', np.nan),
                    'dVdt_max': ap.get('dVdt_max', np.nan),
                    'RMP': ap.get('RMP', np.nan),
                    'APD30': ap.get('APD30', np.nan),
                    'APD50': ap.get('APD50', np.nan),
                    'Repolarization_Fraction': ap.get('Repolarization_Fraction', np.nan)
                })
        
        for cell_id, freq_data in cells.items():
            for frequency, drug_data in freq_data.items():
                for drug, ap_values in drug_data.items():
                    if ap_values:
                        apd90_values = [v['APD90'] for v in ap_values if not math.isnan(v['APD90'])]
                        apa_values = [v['APA'] for v in ap_values if not math.isnan(v['APA'])]
                        dvdt_values = [v['dVdt_max'] for v in ap_values if not math.isnan(v['dVdt_max'])]
                        rmp_values = [v['RMP'] for v in ap_values if not math.isnan(v['RMP'])]
                        apd30_values = [v['APD30'] for v in ap_values if not math.isnan(v['APD30'])]
                        apd50_values = [v['APD50'] for v in ap_values if not math.isnan(v['APD50'])]
                        repol_values = [v['Repolarization_Fraction'] for v in ap_values if not math.isnan(v['Repolarization_Fraction'])]
                        
                        if apd90_values:
                            analysis_data.append({
                                'Cell_ID': cell_id,
                                'Frequency_Hz': frequency,
                                'Drug': drug,
                                'n': len(apd90_values),
                                'APD90_mean_ms': np.mean(apd90_values),
                                'APD90_SEM_ms': np.std(apd90_values) / np.sqrt(len(apd90_values)) if len(apd90_values) > 1 else 0,
                                'APD90_SD_ms': np.std(apd90_values) if len(apd90_values) > 1 else 0,
                                'APA_mean_mV': np.mean(apa_values) if apa_values else np.nan,
                                'APA_SEM_mV': np.std(apa_values) / np.sqrt(len(apa_values)) if apa_values and len(apa_values) > 1 else 0,
                                'dVdt_max_mean_mVms': np.mean(dvdt_values) if dvdt_values else np.nan,
                                'dVdt_max_SEM_mVms': np.std(dvdt_values) / np.sqrt(len(dvdt_values)) if dvdt_values and len(dvdt_values) > 1 else 0,
                                'RMP_mean_mV': np.mean(rmp_values) if rmp_values else np.nan,
                                'RMP_SEM_mV': np.std(rmp_values) / np.sqrt(len(rmp_values)) if rmp_values and len(rmp_values) > 1 else 0,
                                'APD30_mean_ms': np.mean(apd30_values) if apd30_values else np.nan,
                                'APD50_mean_ms': np.mean(apd50_values) if apd50_values else np.nan,
                                'Repolarization_Fraction_mean': np.mean(repol_values) if repol_values else np.nan,
                                'Repolarization_Fraction_SEM': np.std(repol_values) / np.sqrt(len(repol_values)) if repol_values and len(repol_values) > 1 else 0
                            })
        
        if analysis_data:
            df = pd.DataFrame(analysis_data)
            
            with pd.ExcelWriter(filepath, engine='openpyxl') as writer:
                df.to_excel(writer, sheet_name='Frequency_Drug_Response', index=False)
                
                try:
                    pivot_apd90 = pd.pivot_table(df,
                                                 values='APD90_mean_ms',
                                                 index=['Cell_ID', 'Frequency_Hz'],
                                                 columns='Drug',
                                                 aggfunc='first')
                    pivot_apd90.to_excel(writer, sheet_name='APD90_Pivot')
                    
                    pivot_dvdt = pd.pivot_table(df,
                                                values='dVdt_max_mean_mVms',
                                                index=['Cell_ID', 'Frequency_Hz'],
                                                columns='Drug',
                                                aggfunc='first')
                    pivot_dvdt.to_excel(writer, sheet_name='dVdt_Pivot')
                    
                    pivot_repol = pd.pivot_table(df,
                                                 values='Repolarization_Fraction_mean',
                                                 index=['Cell_ID', 'Frequency_Hz'],
                                                 columns='Drug',
                                                 aggfunc='first')
                    pivot_repol.to_excel(writer, sheet_name='Repolarization_Fraction_Pivot')
                
                except Exception as e:
                    print(f"Could not create pivot tables: {e}")
            
            self.add_to_summary(f"Frequency/Drug Response: {filepath.name}")
    
    def export_raw_ap_data_table(self, results, filepath):
        all_data = []
        
        for res in results:
            trace_id = self.get_safe_trace_id(res)
            file_name = res.get('file_name', '')
            cell_id = res.get('cell_id', '')
            freq = res.get('frequency', '')
            drug = res.get('drug', '')
            conc = res.get('concentration', '')
            
            apd_values = [ap.get('APD90', np.nan) for ap in res.get('ap_metrics', [])]
            apd_values = [v for v in apd_values if not math.isnan(v)]
            stv_val = np.nan
            stv_note = ""
            
            if len(apd_values) >= 5:
                stv_val, stv_note = calculate_stv(apd_values)
            
            ap_counter = 0
            for ap in res.get('ap_metrics', []):
                ap_counter += 1
                
                correction_parts = []
                if ap.get('has_manual_correction', False):
                    correction_parts.append('Peak')
                if ap.get('has_manual_upstroke', False):
                    correction_parts.append('Upstroke')
                if ap.get('has_late_repol', False):
                    correction_parts.append('LateRepol')
                
                correction_display = '+'.join(correction_parts) if correction_parts else 'Auto'
                
                row = {
                    'Trace_ID': trace_id,
                    'File': file_name,
                    'Cell_ID': cell_id,
                    'Frequency_Hz': freq,
                    'Drug': drug,
                    'Concentration': conc,
                    'AP_Index': ap_counter,
                    'Correction_Type': correction_display,
                    'Peak_Time_ms': ap.get('peak_time', np.nan),
                    'RMP_mV': ap.get('RMP', np.nan),
                    'RMP_Method': ap.get('RMP_method', ''),
                    'APA_mV': ap.get('APA', np.nan),
                    'dVdt_max_mVms': ap.get('dVdt_max', np.nan),
                    'Overshoot_mV': ap.get('Overshoot', np.nan),
                    'Has_Bump': ap.get('has_bump', False),
                    'Late_Repolarization_Corrected': ap.get('late_repolarization_corrected', False),
                    'Upstroke_Manual': ap.get('upstroke_manual', False),
                    'Repolarization_Fraction': ap.get('Repolarization_Fraction', np.nan)
                }
                
                # Add upstroke quality metrics if available
                if 'upstroke_quality_score' in ap:
                    row['Upstroke_Quality_Score'] = ap.get('upstroke_quality_score', np.nan)
                    row['Upstroke_Quality'] = ap.get('upstroke_quality', 'N/A')
                
                # Add raw APD80/APD90 if late repolarization correction was applied
                if ap.get('late_repolarization_corrected', False):
                    row['APD80_raw_ms'] = ap.get('APD80_raw', np.nan)
                    row['APD90_raw_ms'] = ap.get('APD90_raw', np.nan)
                    row['APD80_corrected_ms'] = ap.get('APD80', np.nan)
                    row['APD90_corrected_ms'] = ap.get('APD90', np.nan)
                else:
                    row['APD80_raw_ms'] = ap.get('APD80', np.nan)
                    row['APD90_raw_ms'] = ap.get('APD90', np.nan)
                    row['APD80_corrected_ms'] = ap.get('APD80', np.nan)
                    row['APD90_corrected_ms'] = ap.get('APD90', np.nan)
                
                for percent in APD_PERCENTAGES:
                    row[f'APD{percent}_ms'] = ap.get(f'APD{percent}', np.nan)
                
                all_data.append(row)
        
        if all_data:
            pd.DataFrame(all_data).to_excel(filepath, index=False)
            self.add_to_summary(f"Raw AP Data Table: {filepath.name}")
    
    def export_individual_traces_csv(self, results, folder):
        exported_count = 0
        
        for i, res in enumerate(results):
            if 'time' not in res or 'voltage_smooth' not in res:
                continue
            
            time_data = res['time']
            voltage_data = res['voltage_smooth']
            
            if len(time_data) == 0 or len(voltage_data) == 0:
                continue
            
            trace_id = self.get_safe_trace_id(res)
            file_name = res.get('file_name', f'trace_{i + 1}')
            cell_id = res.get('cell_id', 'unknown')
            frequency = res.get('frequency', 'unknown')
            drug = res.get('drug', 'None')
            
            # CHANGE 1: Sanitize filename components
            safe_cell = self.sanitize_filename(str(cell_id))
            safe_file = self.sanitize_filename(str(file_name))
            
            filename = f"Trace_{i + 1:04d}_{safe_cell}_{frequency}Hz"
            if drug and drug != 'None':
                safe_drug = self.sanitize_filename(str(drug))
                filename += f"_{safe_drug}"
            filename = self.sanitize_filename(filename, 200) + ".csv"
            
            filepath = folder / filename
            filepath.parent.mkdir(parents=True, exist_ok=True)
            
            df = pd.DataFrame({
                'Time_ms': time_data,
                'Voltage_Raw_mV': res.get('voltage_raw', np.full_like(time_data, np.nan)),
                'Voltage_Smooth_mV': voltage_data
            })
            
            if res.get('ap_metrics'):
                peak_indicator = np.full(len(time_data), 0)
                peak_times = []
                peak_voltages = []
                correction_types = []
                
                for ap in res['ap_metrics']:
                    peak_idx = ap.get('peak_idx')
                    if peak_idx < len(time_data):
                        peak_indicator[peak_idx] = 1
                        peak_times.append(time_data[peak_idx])
                        peak_voltages.append(voltage_data[peak_idx])
                        
                        correction_parts = []
                        if ap.get('has_manual_correction', False):
                            correction_parts.append('Peak')
                        if ap.get('has_manual_upstroke', False):
                            correction_parts.append('Upstroke')
                        if ap.get('has_late_repol', False):
                            correction_parts.append('LateRepol')
                        
                        correction_display = '+'.join(correction_parts) if correction_parts else 'Auto'
                        correction_types.append(correction_display)
                
                df['AP_Peak_Indicator'] = peak_indicator
                
                with open(filepath, 'w') as f:
                    f.write(f"# Individual Action Potential Trace\n")
                    f.write(f"# File: {self.sanitize_filename(file_name)}\n")
                    f.write(f"# Cell ID: {safe_cell}\n")
                    f.write(f"# Frequency: {frequency} Hz\n")
                    f.write(f"# Drug/Condition: {drug}\n")
                    f.write(f"# Concentration: {res.get('concentration', '')}\n")
                    f.write(f"# Species: {res.get('species', 'default')}\n")
                    f.write(f"# n_APs: {len(res.get('ap_metrics', []))}\n")
                    f.write(f"# Corrections: Late Repolarization={any(ap.get('late_repolarization_corrected', False) for ap in res.get('ap_metrics', []))}, "
                           f"Upstroke={any(ap.get('upstroke_manual', False) for ap in res.get('ap_metrics', []))}, "
                           f"Manual Peak={any(ap.get('has_manual_correction', False) for ap in res.get('ap_metrics', []))}\n")
                    
                    if peak_times:
                        f.write(f"# Peak Times (ms): {', '.join([f'{t:.1f}' for t in peak_times])}\n")
                        f.write(f"# Peak Voltages (mV): {', '.join([f'{v:.1f}' for v in peak_voltages])}\n")
                        f.write(f"# Correction Types: {', '.join(correction_types)}\n")
                    
                    f.write("#" * 50 + "\n")
                
                df.to_csv(filepath, mode='a', index=False)
            else:
                df.to_csv(filepath, index=False)
            
            exported_count += 1
        
        self.add_to_summary(f"Individual Traces: {exported_count} CSV files in {folder.name}")
    
    def get_safe_trace_id(self, res):
        trace_id = res.get('trace_id', '')
        file_name = res.get('file_name', 'unknown')
        
        if isinstance(trace_id, tuple):
            trace_str = str(trace_id)
            trace_str = self.sanitize_filename(trace_str, 100)
            return trace_str[:100]
        else:
            trace_str = str(trace_id)
            trace_str = self.sanitize_filename(trace_str, 100)
            return trace_str[:100]
    
    def export_average_traces_csv(self, results, folder):
        import re
        groups = defaultdict(list)
        
        for res in results:
            key = f"{res.get('cell_id')}_{res.get('frequency')}Hz"
            
            drug = res.get('drug', 'None')
            if drug and drug != 'None':
                key += f"_{drug}"
                concentration = res.get('concentration', '')
                if concentration:
                    key += f"_{concentration}"
            
            range_name = res.get('range_name', '')
            if res.get('file_type') == 'CSV/Excel' and range_name:
                if range_name.endswith('.xlsx'):
                    base_name = range_name[:-5]
                elif range_name.endswith('.csv'):
                    base_name = range_name[:-4]
                else:
                    base_name = range_name
                
                base_range = re.sub(r'_\d+$', '', base_name)
                key += f"_{base_range}"
            elif range_name and res.get('file_type') == 'ABF':
                key += f"_{range_name}"
            
            groups[key].append(res)
        
        avg_count = 0
        for condition_key, group_results in groups.items():
            if len(group_results) < 1:
                continue
            
            frequency = group_results[0].get('frequency', '1.0')
            
            sweep_numbers = []
            for res in group_results:
                range_name = res.get('range_name', '')
                if range_name and (range_name.endswith('.xlsx') or range_name.endswith('.csv')):
                    import re
                    if range_name.endswith('.xlsx'):
                        base = range_name[:-5]
                    else:
                        base = range_name[:-4]
                    
                    match = re.search(r'_(\d+)$', base)
                    if match:
                        sweep_numbers.append(int(match.group(1)))
            
            aligned = self.align_and_average_traces(group_results)
            if aligned:
                # CHANGE 1: Sanitize condition key for filename
                safe_condition = self.sanitize_filename(str(condition_key))
                
                if sweep_numbers and len(sweep_numbers) > 1:
                    sweep_range = f"_sw{min(sweep_numbers)}-{max(sweep_numbers)}"
                elif sweep_numbers:
                    sweep_range = f"_sw{sweep_numbers[0]}"
                else:
                    sweep_range = ""
                
                filename = f"Average_{safe_condition}{sweep_range}.csv"
                filename = self.sanitize_filename(filename, 200)
                filepath = folder / filename
                
                df = pd.DataFrame({
                    'Time_ms': aligned['time'],
                    'Voltage_Avg_mV': aligned['voltage_avg'],
                    'Voltage_SEM_mV': aligned['voltage_sem'],
                    'n_traces': aligned['n_traces']
                })
                
                with open(filepath, 'w') as f:
                    f.write(f"# Average Action Potential Trace\n")
                    f.write(f"# Condition: {condition_key}\n")
                    f.write(f"# n_traces: {aligned['n_traces']}\n")
                    f.write(f"# Alignment: Based on first AP peak\n")
                    f.write(f"# Window: -50ms to +{aligned.get('window_after_ms', 300)}ms around peak\n")
                    f.write(f"# Frequency: {frequency} Hz\n")
                    f.write(f"# Files in average: {len(group_results)}\n")
                    
                    if group_results:
                        f.write(f"# Files averaged:\n")
                        for res in group_results[:5]:
                            f.write(f"#   - {res.get('file_name', 'unknown')}\n")
                        if len(group_results) > 5:
                            f.write(f"#   ... and {len(group_results) - 5} more\n")
                    
                    if sweep_numbers:
                        f.write(f"# Sweep numbers: {sorted(sweep_numbers)}\n")
                    
                    f.write("#" * 50 + "\n")
                
                df.to_csv(filepath, mode='a', index=False)
                avg_count += 1
        
        self.add_to_summary(f"Average Traces: {avg_count} CSV files in {folder.name}")
    
    def align_and_average_traces(self, traces, window_before_ms=50, window_after_ms=300):
        aligned_voltage_arrays = []
        
        for res in traces:
            if not res.get('ap_metrics'):
                continue
            
            first_ap = res['ap_metrics'][0]
            peak_time = first_ap['peak_time']
            peak_idx = first_ap['peak_idx']
            
            frequency = res.get('frequency', '1.0')
            
            if frequency == '0.5':
                window_after_ms = 2000
            elif frequency == '1.0':
                window_after_ms = 1000
            elif frequency == '2.0':
                window_after_ms = 500
            elif frequency == '3.0':
                window_after_ms = 500
            elif frequency == '4.0':
                window_after_ms = 250
            elif frequency == '5.0':
                window_after_ms = 200
            else:
                window_after_ms = 300
            
            dt = res['dt_ms']
            start_idx = max(0, peak_idx - int(window_before_ms / dt))
            end_idx = min(len(res['time']), peak_idx + int(window_after_ms / dt))
            
            time_window = res['time'][start_idx:end_idx] - peak_time
            voltage_window = res['voltage_smooth'][start_idx:end_idx]
            
            common_time = np.linspace(-window_before_ms, window_after_ms, 500)
            
            if len(time_window) > 1:
                interp_voltage = np.interp(common_time, time_window, voltage_window)
                aligned_voltage_arrays.append(interp_voltage)
        
        if not aligned_voltage_arrays:
            return None
        
        voltage_matrix = np.array(aligned_voltage_arrays)
        voltage_avg = np.mean(voltage_matrix, axis=0)
        voltage_sem = np.std(voltage_matrix, axis=0) / np.sqrt(len(aligned_voltage_arrays))
        
        return {
            'time': common_time,
            'voltage_avg': voltage_avg,
            'voltage_sem': voltage_sem,
            'n_traces': len(aligned_voltage_arrays),
            'window_after_ms': window_after_ms
        }
    
    def export_enhanced_figures(self, results, folder, figure_types):
        for fig_type in figure_types:
            fig_folder = folder / fig_type
            fig_folder.mkdir(exist_ok=True)
    
        if 'ap_overlay_raw' in figure_types:
            if self.one_figure_per_cell:
                self.create_ap_overlay_raw_per_cell_figures(results, folder / 'ap_overlay_raw')
            else:
                self.create_ap_overlay_raw_figures(results, folder / 'ap_overlay_raw')
    
        if 'average_ap_sem' in figure_types:
            if self.one_figure_per_cell:
                self.create_average_ap_sem_per_cell_figures(results, folder / 'average_ap_sem')
            else:
                self.create_average_ap_sem_figures(results, folder / 'average_ap_sem')
        
        if 'drug_comparison' in figure_types:
            self.create_drug_comparison_figures(results, folder / 'drug_comparison')
        
        if 'frequency_comparison' in figure_types:
            self.create_frequency_comparison_figures(results, folder / 'frequency_comparison')
        
        if 'stv_analysis' in figure_types:
            self.create_poincare_plot_figures(results, folder / 'stv_analysis')
        
        if 'normalized_ap' in figure_types:
            self.create_normalized_ap_figures(results, folder / 'normalized_ap')
    
    def create_ap_overlay_raw_figures(self, results, folder):
        groups = defaultdict(list)
        for res in results:
            key = (res.get('cell_id'), res.get('drug'), res.get('frequency'))
            groups[key].append(res)
        
        for (cell_id, drug, freq), group_results in groups.items():
            if len(group_results) < 2:
                continue
            
            fig, ax = plt.subplots(figsize=(12, 8))
            
            control_color = '#333333'
            drug_color = '#6A0DAD'
            trace_color = control_color if drug == 'None' or drug == 'Control' else drug_color
            
            for i, res in enumerate(group_results):
                alpha = 0.3 + (0.7 * i / len(group_results))
                linewidth = 0.8 if i < len(group_results) - 1 else 2.0
                
                ax.plot(res['time'], res['voltage_raw'],
                        color=trace_color, alpha=alpha, linewidth=linewidth)
            
            ax.set_xlabel('Time (ms)', fontsize=14, fontweight='bold')
            ax.set_ylabel('Voltage (mV)', fontsize=14, fontweight='bold')
            
            title = f'Beat-to-Beat Variability - {cell_id}'
            if freq and freq != 'unknown':
                title += f' ({freq} Hz)'
            if drug and drug != 'None':
                title += f' - {drug}'
            
            ax.set_title(title, fontsize=16, fontweight='bold')
            ax.grid(True, alpha=0.2)
            
            if freq in FREQUENCY_XLIMITS:
                ax.set_xlim(0, FREQUENCY_XLIMITS[freq])
            
            filename = f"AP_Overlay_RAW_{self.sanitize_filename(cell_id)}_{freq}Hz"
            if drug and drug != 'None':
                filename += f"_{self.sanitize_filename(drug)}"
            filename = self.sanitize_filename(filename, 200) + ".png"
            
            filepath = folder / filename
            plt.tight_layout()
            plt.savefig(filepath, dpi=300, bbox_inches='tight')
            plt.close()
        
        self.add_to_summary(f"AP Overlay (RAW) Figures: {len(groups)} in {folder.name}")
    
    def create_ap_overlay_raw_per_cell_figures(self, results, folder):
        """CRITICAL FIX: Group by cell ID only (ignore drug/condition for overlay)"""
        cells = defaultdict(list)
        
        # Group by cell ID only (ignore drug/condition for overlay)
        for res in results:
            cell_id = res.get('cell_id', 'unknown')
            cells[cell_id].append(res)
        
        for cell_id, cell_results in cells.items():
            if len(cell_results) < 2:
                continue
            
            # Group by frequency within this cell
            freq_groups = defaultdict(list)
            for res in cell_results:
                freq = res.get('frequency', 'unknown')
                drug = res.get('drug', 'None')
                condition_key = f"{freq}Hz"
                if drug and drug != 'None':
                    condition_key += f"_{drug}"
                freq_groups[condition_key].append(res)
            
            fig, ax = plt.subplots(figsize=(14, 8))
            
            colors = plt.cm.tab10(np.linspace(0, 1, len(freq_groups)))
            color_idx = 0
            
            legend_handles = []
            legend_labels = []
            
            for condition_key, group_results in freq_groups.items():
                if len(group_results) < 1:
                    continue
                
                color = colors[color_idx % len(colors)]
                color_idx += 1                
                for i, res in enumerate(group_results):
                    alpha = 0.3 + (0.7 * i / len(group_results))
                    linewidth = 0.8
                    
                    line = ax.plot(res['time'], res['voltage_raw'],
                                   color=color, alpha=alpha, linewidth=linewidth)[0]
                
                legend_handles.append(line)
                legend_labels.append(condition_key)
            
            ax.set_xlabel('Time (ms)', fontsize=14, fontweight='bold')
            ax.set_ylabel('Voltage (mV)', fontsize=14, fontweight='bold')
            
            title = f'Frequency Comparison - {cell_id}'
            ax.set_title(title, fontsize=16, fontweight='bold')
            ax.grid(True, alpha=0.2)
            
            # Set x-axis based on highest frequency in this cell
            max_freq = max([float(r.get('frequency', '1.0')) for r in cell_results if r.get('frequency', '1.0') != 'unknown'], default=1.0)
            freq_key = f"{max_freq:.1f}" if isinstance(max_freq, float) else str(max_freq)
            if freq_key in FREQUENCY_XLIMITS:
                ax.set_xlim(0, FREQUENCY_XLIMITS[freq_key])
            
            ax.legend(legend_handles, legend_labels, fontsize=10, loc='upper right')
            
            safe_cell_id = self.sanitize_filename(str(cell_id))
            filename = f"AP_Overlay_RAW_{safe_cell_id}_Frequency_Comparison.png"
            filename = self.sanitize_filename(filename, 200)
            filepath = folder / filename
            plt.tight_layout()
            plt.savefig(filepath, dpi=300, bbox_inches='tight')
            plt.close()
        
        self.add_to_summary(f"AP Overlay (RAW) Figures (1 per cell): {len(cells)} cells in {folder.name}")
    
    def create_average_ap_sem_figures(self, results, folder):
        groups = defaultdict(list)
        for res in results:
            key = (res.get('cell_id'), res.get('drug'), res.get('frequency'))
            groups[key].append(res)
        
        for (cell_id, drug, freq), group_results in groups.items():
            if len(group_results) < 2:
                continue
            
            aligned = self.align_and_average_traces(group_results, window_before_ms=50, window_after_ms=300)
            if not aligned:
                continue
            
            fig, ax = plt.subplots(figsize=(12, 8))
            
            trace_color = '#333333' if drug == 'None' or drug == 'Control' else '#6A0DAD'
            
            ax.plot(aligned['time'], aligned['voltage_avg'],
                    color=trace_color, linewidth=3, label='Mean AP')
            ax.fill_between(aligned['time'],
                            aligned['voltage_avg'] - aligned['voltage_sem'],
                            aligned['voltage_avg'] + aligned['voltage_sem'],
                            color=trace_color, alpha=0.2, label='± SEM')
            
            # Ensure x-axis starts at -50 ms to show full AP including upstroke
            ax.set_xlim(-50, ax.get_xlim()[1])
            ax.set_xlabel('Time (ms)', fontsize=14, fontweight='bold')
            ax.set_ylabel('Voltage (mV)', fontsize=14, fontweight='bold')
            
            title = f'Average AP ± SEM - {cell_id}'
            if freq and freq != 'unknown':
                title += f' ({freq} Hz)'
            if drug and drug != 'None':
                title += f' - {drug}'
            
            ax.set_title(title, fontsize=16, fontweight='bold')
            ax.legend(fontsize=12, loc='upper right')
            ax.grid(True, alpha=0.2)
            
            filename = f"Average_AP_SEM_{self.sanitize_filename(cell_id)}_{freq}Hz"
            if drug and drug != 'None':
                filename += f"_{self.sanitize_filename(drug)}"
            filename = self.sanitize_filename(filename, 200) + ".png"
            
            filepath = folder / filename
            plt.tight_layout()
            plt.savefig(filepath, dpi=300, bbox_inches='tight')
            plt.close()
        
        self.add_to_summary(f"Average AP ± SEM Figures: {len(groups)} in {folder.name}")
    
    def create_average_ap_sem_per_cell_figures(self, results, folder):
        """CRITICAL FIX: One figure per cell showing all frequencies"""
        cells = defaultdict(list)
        
        for res in results:
            cell_id = res.get('cell_id', 'unknown')
            cells[cell_id].append(res)
        
        for cell_id, cell_results in cells.items():
            if len(cell_results) < 2:
                continue
            
            # Group by frequency within this cell
            freq_groups = defaultdict(list)
            for res in cell_results:
                freq = res.get('frequency', 'unknown')
                drug = res.get('drug', 'None')
                condition_key = f"{freq}Hz"
                if drug and drug != 'None':
                    condition_key += f"_{drug}"
                freq_groups[condition_key].append(res)
            
            if len(freq_groups) < 2:
                continue
            
            fig, ax = plt.subplots(figsize=(14, 8))
            
            colors = plt.cm.tab10(np.linspace(0, 1, len(freq_groups)))
            color_idx = 0
            
            legend_handles = []
            legend_labels = []
            
            for condition_key, group_results in freq_groups.items():
                if len(group_results) < 1:
                    continue
                
                color = colors[color_idx % len(colors)]
                color_idx += 1
                
                aligned = self.align_and_average_traces(group_results, window_before_ms=50, window_after_ms=300)
                if not aligned:
                    continue
                
                line = ax.plot(aligned['time'], aligned['voltage_avg'],
                               color=color, linewidth=3)[0]
                ax.fill_between(aligned['time'],
                                aligned['voltage_avg'] - aligned['voltage_sem'],
                                aligned['voltage_avg'] + aligned['voltage_sem'],
                                color=color, alpha=0.2)
                
                legend_handles.append(line)
                legend_labels.append(f"{condition_key} (n={aligned['n_traces']})")
            
            ax.set_xlabel('Time (ms)', fontsize=14, fontweight='bold')
            ax.set_ylabel('Voltage (mV)', fontsize=14, fontweight='bold')
            
            title = f'Frequency Comparison - {cell_id}'
            ax.set_title(title, fontsize=16, fontweight='bold')
            ax.grid(True, alpha=0.2)
            
            # Set x-axis based on highest frequency
            max_freq = max([float(r.get('frequency', '1.0')) for r in cell_results if r.get('frequency', '1.0') != 'unknown'], default=1.0)
            freq_key = f"{max_freq:.1f}" if isinstance(max_freq, float) else str(max_freq)
            if freq_key in FREQUENCY_XLIMITS:
                ax.set_xlim(-50, FREQUENCY_XLIMITS[freq_key])
            else:
                ax.set_xlim(-50, ax.get_xlim()[1])
            
            ax.legend(legend_handles, legend_labels, fontsize=10, loc='upper right')
            
            safe_cell_id = self.sanitize_filename(str(cell_id))
            filename = f"Average_AP_SEM_{safe_cell_id}_Frequency_Comparison.png"
            filename = self.sanitize_filename(filename, 200)
            filepath = folder / filename
            plt.tight_layout()
            plt.savefig(filepath, dpi=300, bbox_inches='tight')
            plt.close()
        
        self.add_to_summary(f"Average AP ± SEM Figures (1 per cell): {len(cells)} cells in {folder.name}")
    
    def create_drug_comparison_figures(self, results, folder):
        cell_drugs = defaultdict(set)
        cell_data = defaultdict(lambda: {'ap_data': [], 'traces': []})
        
        for res in results:
            cell_id = res.get('cell_id', '')
            drug = res.get('drug', 'None')
            freq = res.get('frequency', '')
            
            if not cell_id or not freq:
                continue
            
            cell_drugs[cell_id].add((drug, freq))
            
            if res.get('ap_metrics'):
                for ap in res.get('ap_metrics', []):
                    cell_data[(cell_id, drug, freq)]['ap_data'].append({
                        'APD90': ap.get('APD90', np.nan),
                        'APA': ap.get('APA', np.nan),
                        'RMP': ap.get('RMP', np.nan),
                        'dVdt_max': ap.get('dVdt_max', np.nan)
                    })
                cell_data[(cell_id, drug, freq)]['traces'].append(res)
        
        valid_cells = []
        for cell_id, drug_freqs in cell_drugs.items():
            freq_data = defaultdict(set)
            for drug, freq in drug_freqs:
                freq_data[freq].add(drug)
            
            for freq, drugs in freq_data.items():
                if ('None' in drugs or 'Control' in drugs) and len(drugs) > 1:
                    other_drugs = [d for d in drugs if d not in ['None', 'Control']]
                    if other_drugs:
                        valid_cells.append((cell_id, freq, other_drugs[0]))
        
        if not valid_cells:
            return
        
        for cell_id, freq, drug in valid_cells:
            fig = plt.figure(figsize=(16, 10))
            
            gs = GridSpec(2, 2, figure=fig, hspace=0.3, wspace=0.3)
            ax1 = fig.add_subplot(gs[0, 0])
            ax2 = fig.add_subplot(gs[0, 1])
            ax3 = fig.add_subplot(gs[1, 0])
            ax4 = fig.add_subplot(gs[1, 1])
            
            control_key = (cell_id, 'None', freq) if (cell_id, 'None', freq) in cell_data else (cell_id, 'Control', freq)
            drug_key = (cell_id, drug, freq)
            
            control_data = cell_data.get(control_key, {}).get('ap_data', [])
            drug_data = cell_data.get(drug_key, {}).get('ap_data', [])
            
            control_traces = cell_data.get(control_key, {}).get('traces', [])
            drug_traces = cell_data.get(drug_key, {}).get('traces', [])
            
            if not control_data or not drug_data:
                continue
            
            if control_traces and drug_traces:
                control_aligned = self.align_and_average_traces(control_traces, window_before_ms=50, window_after_ms=300)
                drug_aligned = self.align_and_average_traces(drug_traces, window_before_ms=50, window_after_ms=300)
                
                if control_aligned and drug_aligned:
                    ax1.plot(control_aligned['time'], control_aligned['voltage_avg'],
                             color='#333333', linewidth=3, label='Control')
                    ax1.fill_between(control_aligned['time'],
                                     control_aligned['voltage_avg'] - control_aligned['voltage_sem'],
                                     control_aligned['voltage_avg'] + control_aligned['voltage_sem'],
                                     color='#333333', alpha=0.2)
                    
                    ax1.plot(drug_aligned['time'], drug_aligned['voltage_avg'],
                             color='#6A0DAD', linewidth=3, label=drug)
                    ax1.fill_between(drug_aligned['time'],
                                     drug_aligned['voltage_avg'] - drug_aligned['voltage_sem'],
                                     drug_aligned['voltage_avg'] + drug_aligned['voltage_sem'],
                                     color='#6A0DAD', alpha=0.2)
            
            ax1.set_xlabel('Time (ms)', fontsize=11)
            ax1.set_ylabel('Voltage (mV)', fontsize=11)
            ax1.set_title('A. AP Morphology', fontsize=12, fontweight='bold')
            ax1.legend(fontsize=10)
            ax1.grid(True, alpha=0.2)
            
            control_apd90 = [d['APD90'] for d in control_data if not math.isnan(d['APD90'])]
            drug_apd90 = [d['APD90'] for d in drug_data if not math.isnan(d['APD90'])]
            
            if control_apd90 and drug_apd90:
                positions = [1, 2]
                means = [np.mean(control_apd90), np.mean(drug_apd90)]
                sems = [np.std(control_apd90) / np.sqrt(len(control_apd90)) if len(control_apd90) > 1 else 0,
                        np.std(drug_apd90) / np.sqrt(len(drug_apd90)) if len(drug_apd90) > 1 else 0]
                
                ax2.bar(positions, means, yerr=sems, capsize=10,
                        color=['#333333', '#6A0DAD'], edgecolor='black')
                ax2.set_xticks(positions)
                ax2.set_xticklabels(['Control', drug])
                ax2.set_ylabel('APD90 (ms)', fontsize=11)
                ax2.set_title('B. APD90 Comparison', fontsize=12, fontweight='bold')
                ax2.grid(True, alpha=0.2, axis='y')
            
            control_dvdt = [d['dVdt_max'] for d in control_data if not math.isnan(d['dVdt_max'])]
            drug_dvdt = [d['dVdt_max'] for d in drug_data if not math.isnan(d['dVdt_max'])]
            
            if control_dvdt and drug_dvdt:
                data_to_plot = [control_dvdt, drug_dvdt]
                bp = ax3.boxplot(data_to_plot, tick_labels=['Control', drug],
                                 patch_artist=True)
                
                bp['boxes'][0].set_facecolor('#333333')
                bp['boxes'][1].set_facecolor('#6A0DAD')
                
                ax3.set_ylabel('dV/dt_max (mV/ms)', fontsize=11)
                ax3.set_title('C. Upstroke Velocity', fontsize=12, fontweight='bold')
                ax3.grid(True, alpha=0.2, axis='y')
            
            control_rmp = [d['RMP'] for d in control_data if not math.isnan(d['RMP'])]
            control_apa = [d['APA'] for d in control_data if not math.isnan(d['APA'])]
            drug_rmp = [d['RMP'] for d in drug_data if not math.isnan(d['RMP'])]
            drug_apa = [d['APA'] for d in drug_data if not math.isnan(d['APA'])]
            
            if control_rmp and control_apa and drug_rmp and drug_apa:
                ax4.scatter(control_rmp, control_apa, color='#333333',
                            s=50, alpha=0.7, label='Control')
                ax4.scatter(drug_rmp, drug_apa, color='#6A0DAD',
                            s=50, alpha=0.7, label=drug)
                
                ax4.set_xlabel('RMP (mV)', fontsize=11)
                ax4.set_ylabel('APA (mV)', fontsize=11)
                ax4.set_title('D. RMP vs APA', fontsize=12, fontweight='bold')
                ax4.legend(fontsize=10)
                ax4.grid(True, alpha=0.2)
            
            plt.suptitle(f'Drug Comparison: {cell_id} ({freq} Hz)',
                         fontsize=16, fontweight='bold', y=0.98)
            plt.tight_layout(rect=[0, 0, 1, 0.96])
            
            filename = f"Drug_Comparison_{self.sanitize_filename(cell_id)}_{self.sanitize_filename(drug)}_{freq}Hz.png"
            filename = self.sanitize_filename(filename, 200)
            filepath = folder / filename
            plt.savefig(filepath, dpi=300, bbox_inches='tight')
            plt.close()
        
        self.add_to_summary(f"Drug Comparison Figures: {len(valid_cells)} in {folder.name}")
    
    def create_frequency_comparison_figures(self, results, folder):
        cell_freqs = defaultdict(set)
        cell_data = defaultdict(lambda: {'ap_data': [], 'trace_data': []})
        
        for res in results:
            cell_id = res.get('cell_id', '')
            drug = res.get('drug', 'None')
            freq = res.get('frequency', '')
            
            if not cell_id or not freq or freq == 'unknown':
                continue
            
            if drug not in ['None', 'Control']:
                continue
            
            cell_freqs[cell_id].add(freq)
            
            if res.get('ap_metrics'):
                for ap in res.get('ap_metrics', []):
                    cell_data[(cell_id, freq)]['ap_data'].append({
                        'APD90': ap.get('APD90', np.nan),
                        'APA': ap.get('APA', np.nan),
                        'RMP': ap.get('RMP', np.nan),
                        'dVdt_max': ap.get('dVdt_max', np.nan)
                    })
                cell_data[(cell_id, freq)]['trace_data'].append(res)
        
        valid_cells = []
        for cell_id, freqs in cell_freqs.items():
            if len(freqs) >= 2:
                valid_cells.append((cell_id, sorted(list(freqs))))
        
        if not valid_cells:
            return
        
        for cell_id, freqs in valid_cells:
            if len(freqs) < 2:
                continue
            
            fig = plt.figure(figsize=(16, 10))
            
            gs = GridSpec(2, 2, figure=fig, hspace=0.3, wspace=0.3)
            ax1 = fig.add_subplot(gs[0, 0])
            ax2 = fig.add_subplot(gs[0, 1])
            ax3 = fig.add_subplot(gs[1, 0])
            ax4 = fig.add_subplot(gs[1, 1])
            
            freq_data = {}
            freq_traces = {}
            
            for freq in freqs[:4]:
                key = (cell_id, freq)
                if key in cell_data:
                    freq_data[freq] = cell_data[key]['ap_data']
                    freq_traces[freq] = cell_data[key]['trace_data']
            
            if len(freq_data) < 2:
                continue
            
            colors = plt.cm.viridis(np.linspace(0.2, 0.8, len(freq_data)))
            color_idx = 0
            
            for freq, traces in freq_traces.items():
                if traces:
                    aligned = self.align_and_average_traces(traces, window_before_ms=50, window_after_ms=300)
                    if aligned:
                        color = colors[color_idx]
                        ax1.plot(aligned['time'], aligned['voltage_avg'],
                                 color=color, linewidth=3, label=f'{freq} Hz')
                        ax1.fill_between(aligned['time'],
                                         aligned['voltage_avg'] - aligned['voltage_sem'],
                                         aligned['voltage_avg'] + aligned['voltage_sem'],
                                         color=color, alpha=0.2)
                        color_idx += 1
            
            ax1.set_xlabel('Time (ms)', fontsize=11)
            ax1.set_ylabel('Voltage (mV)', fontsize=11)
            ax1.set_title('A. AP Morphology', fontsize=12, fontweight='bold')
            ax1.legend(fontsize=10)
            ax1.grid(True, alpha=0.2)
            
            freq_apd90 = {}
            for freq, data in freq_data.items():
                apd90_vals = [d['APD90'] for d in data if not math.isnan(d['APD90'])]
                if apd90_vals:
                    freq_apd90[freq] = apd90_vals
            
            if freq_apd90:
                freqs_sorted = sorted(freq_apd90.keys())
                positions = range(len(freqs_sorted))
                means = [np.mean(freq_apd90[f]) for f in freqs_sorted]
                sems = [np.std(freq_apd90[f]) / np.sqrt(len(freq_apd90[f])) if len(freq_apd90[f]) > 1 else 0
                        for f in freqs_sorted]
                
                bars = ax2.bar(positions, means, yerr=sems, capsize=10,
                               color=colors[:len(freqs_sorted)], edgecolor='black')
                ax2.set_xticks(positions)
                ax2.set_xticklabels([f'{f} Hz' for f in freqs_sorted])
                ax2.set_ylabel('APD90 (ms)', fontsize=11)
                ax2.set_title('B. APD90 Comparison', fontsize=12, fontweight='bold')
                ax2.grid(True, alpha=0.2, axis='y')
            
            freq_dvdt = {}
            for freq, data in freq_data.items():
                dvdt_vals = [d['dVdt_max'] for d in data if not math.isnan(d['dVdt_max'])]
                if dvdt_vals:
                    freq_dvdt[freq] = dvdt_vals
            
            if freq_dvdt:
                data_to_plot = [freq_dvdt[f] for f in sorted(freq_dvdt.keys())]
                labels = [f'{f} Hz' for f in sorted(freq_dvdt.keys())]
                bp = ax3.boxplot(data_to_plot, tick_labels=labels, patch_artist=True)
                
                for i, box in enumerate(bp['boxes']):
                    box.set_facecolor(colors[i])
                
                ax3.set_ylabel('dV/dt_max (mV/ms)', fontsize=11)
                ax3.set_title('C. Upstroke Velocity', fontsize=12, fontweight='bold')
                ax3.grid(True, alpha=0.2, axis='y')
                ax3.tick_params(axis='x', rotation=45)
            
            for i, (freq, data) in enumerate(freq_data.items()):
                if i >= len(colors):
                    break
                
                rmp_vals = [d['RMP'] for d in data if not math.isnan(d['RMP'])]
                apa_vals = [d['APA'] for d in data if not math.isnan(d['APA'])]
                
                if rmp_vals and apa_vals:
                    ax4.scatter(rmp_vals, apa_vals, color=colors[i],
                                s=50, alpha=0.7, label=f'{freq} Hz')
            
            ax4.set_xlabel('RMP (mV)', fontsize=11)
            ax4.set_ylabel('APA (mV)', fontsize=11)
            ax4.set_title('D. RMP vs APA', fontsize=12, fontweight='bold')
            ax4.legend(fontsize=10)
            ax4.grid(True, alpha=0.2)
            
            plt.suptitle(f'Frequency Comparison: {cell_id}',
                         fontsize=16, fontweight='bold', y=0.98)
            plt.tight_layout(rect=[0, 0, 1, 0.96])
            
            safe_cell_id = self.sanitize_filename(str(cell_id))
            filename = f"Frequency_Comparison_{safe_cell_id}.png"
            filename = self.sanitize_filename(filename, 200)
            filepath = folder / filename
            plt.savefig(filepath, dpi=300, bbox_inches='tight')
            plt.close()
        
        self.add_to_summary(f"Frequency Comparison Figures: {len(valid_cells)} in {folder.name}")
    
    def create_poincare_plot_figures(self, results, folder):
        folder.mkdir(parents=True, exist_ok=True)
        
        grouped_results = defaultdict(list)
        
        for res in results:
            cell_id = res.get('cell_id', 'unknown')
            drug = res.get('drug', 'None')
            freq = res.get('frequency', 'unknown')
            
            key = f"{cell_id}_{drug}_{freq}Hz"
            if drug in ['None', 'Control']:
                key = f"{cell_id}_Control_{freq}Hz"
            
            grouped_results[key].append(res)
        
        plots_created = 0
        
        for condition, result_group in grouped_results.items():
            all_apd90_values = []
            
            for res in result_group:
                if 'ap_metrics' in res:
                    for ap in res['ap_metrics']:
                        apd90 = ap.get('APD90')
                        if apd90 is not None and not math.isnan(apd90):
                            all_apd90_values.append(apd90)
            
            if len(all_apd90_values) < 5:
                continue
            
            try:
                fig, ax = plt.subplots(figsize=(10, 10))
                
                apd_n = all_apd90_values[:-1]
                apd_n1 = all_apd90_values[1:]
                
                scatter = ax.scatter(apd_n, apd_n1,
                                     c=np.arange(len(apd_n)),
                                     cmap='viridis',
                                     s=100,
                                     alpha=0.7,
                                     edgecolors='black',
                                     linewidth=0.5)
                
                max_val = max(all_apd90_values)
                min_val = min(all_apd90_values)
                ax.plot([min_val, max_val], [min_val, max_val],
                        'k--', alpha=0.5, linewidth=2,
                        label='Identity line (y = x)')
                
                stv_val, stv_note = calculate_stv(all_apd90_values)
                
                differences = np.array(apd_n1) - np.array(apd_n)
                sd1 = np.std(differences) / np.sqrt(2) if len(differences) > 1 else 0
                sums = [apd_n[i] + apd_n1[i] for i in range(len(apd_n))]
                sd2 = np.std(sums) / np.sqrt(2) if len(sums) > 1 else 0
                
                mean_x = np.mean(apd_n)
                mean_y = np.mean(apd_n1)
                
                if sd1 > 0 and sd2 > 0:
                    ellipse = Ellipse((mean_x, mean_y),
                                      width=2 * sd2,
                                      height=2 * sd1,
                                      angle=45,
                                      alpha=0.2,
                                      color='red',
                                      label='SD1/SD2 ellipse')
                    ax.add_patch(ellipse)
                
                ax.set_xlabel('APD$_n$ (ms)', fontsize=14, fontweight='bold')
                ax.set_ylabel('APD$_{n+1}$ (ms)', fontsize=14, fontweight='bold')
                
                title = f'Poincaré Plot\n{condition}\n'
                title += f'STV = {stv_val:.3f}, SD1 = {sd1:.2f} ms, SD2 = {sd2:.2f} ms'
                ax.set_title(title, fontsize=16, fontweight='bold', pad=20)
                
                ax.grid(True, alpha=0.3)
                ax.set_aspect('equal')
                
                cbar = plt.colorbar(scatter, ax=ax)
                cbar.set_label('Beat Number', fontsize=12)
                
                metrics_text = (
                    f'Mean APD90: {np.mean(all_apd90_values):.1f} ms\n'
                    f'SD APD90: {np.std(all_apd90_values):.1f} ms\n'
                    f'STV: {stv_val:.3f}\n'
                    f'SD1: {sd1:.2f} ms\n'
                    f'SD2: {sd2:.2f} ms\n'
                    f'SD1/SD2 ratio: {sd1 / sd2:.2f}\n'
                    f'n beats: {len(all_apd90_values)}'
                )
                
                ax.text(0.02, 0.98, metrics_text,
                        transform=ax.transAxes,
                        fontsize=10,
                        verticalalignment='top',
                        bbox=dict(boxstyle='round',
                                  facecolor='lightyellow',
                                  alpha=0.9))
                
                ax.legend(loc='lower right', fontsize=10)
                
                plt.tight_layout()
                
                safe_condition = self.sanitize_filename(condition)
                filename = f"Poincare_Plot_{safe_condition}.png"
                filename = self.sanitize_filename(filename, 200)
                filepath = folder / filename
                plt.savefig(filepath, dpi=300, bbox_inches='tight')
                plt.close()
                
                plots_created += 1
            
            except Exception as e:
                print(f"Error creating Poincaré plot for {condition}: {str(e)}")
                traceback.print_exc()
                continue
        
        self.add_to_summary(f"Poincaré Plot Figures: {plots_created} in {folder.name}")
        
        return plots_created
    
    def create_normalized_ap_figures(self, results, folder):
        groups = defaultdict(list)
        
        for res in results:
            key = (res.get('cell_id'), res.get('drug'))
            groups[key].append(res)
        
        for (cell_id, drug), group_results in groups.items():
            if len(group_results) < 2:
                continue
            
            fig, ax = plt.subplots(figsize=(12, 8))
            
            color = '#333333' if drug == 'None' or drug == 'Control' else '#6A0DAD'
            
            for i, res in enumerate(group_results):
                if not res.get('ap_metrics'):
                    continue
                
                ap = res['ap_metrics'][0]
                rmp = ap.get('RMP', 0)
                apa = ap.get('APA', 1)
                peak_idx = ap.get('peak_idx', 0)
                
                if peak_idx >= len(res['time']):
                    continue
                
                window_ms = 300
                dt = res['dt_ms']
                window_samples = int(window_ms / dt)
                start_idx = max(0, peak_idx - window_samples // 2)
                end_idx = min(len(res['time']), peak_idx + window_samples // 2)
                
                time_window = res['time'][start_idx:end_idx] - res['time'][peak_idx]
                voltage_window = res['voltage_smooth'][start_idx:end_idx]
                
                v_norm = (voltage_window - rmp) / apa if apa != 0 else voltage_window
                
                ax.plot(time_window, v_norm, color=color, alpha=0.6, linewidth=1.5)
            
            ax.set_xlabel('Time (ms)', fontsize=14, fontweight='bold')
            ax.set_ylabel('Normalized Voltage', fontsize=14, fontweight='bold')
            
            title = f'Normalized AP Overlay - {cell_id}'
            if drug and drug != 'None':
                title += f' - {drug}'
            
            ax.set_title(title, fontsize=16, fontweight='bold')
            ax.grid(True, alpha=0.2)
            
            filename = f"Normalized_AP_{self.sanitize_filename(cell_id)}"
            if drug and drug != 'None':
                filename += f"_{self.sanitize_filename(drug)}"
            filename = self.sanitize_filename(filename, 200) + ".png"
            
            filepath = folder / filename
            plt.tight_layout()
            plt.savefig(filepath, dpi=300, bbox_inches='tight')
            plt.close()
        
        self.add_to_summary(f"Normalized AP Figures: {len(groups)} in {folder.name}")


# ============================================================================
# Utility Functions
# ============================================================================

def fuzzy_find_columns(df):
    """Return (time_col, voltage_col)"""
    cols = [c for c in df.columns]
    ignore_tokens = ['sweep', 'index', 'id', 'cell', 'well']
    filtered = []
    for c in cols:
        low = c.lower()
        if any(tok in low and ('sweep' in low or tok in low) for tok in ['sweep', 'index', 'id']):
            continue
        filtered.append(c)
    
    time_col = None
    voltage_col = None
    for pattern in TIME_KEYS:
        for c in filtered:
            if pattern in c.lower().replace(' ', '').replace('(', '').replace(')', ''):
                time_col = c
                break
        if time_col:
            break
    for pattern in VOLT_KEYS:
        for c in filtered:
            if pattern in c.lower().replace(' ', '').replace('(', '').replace(')', ''):
                voltage_col = c
                break
        if voltage_col:
            break
    
    if not time_col or not voltage_col:
        numeric_cols = [c for c in filtered if pd.api.types.is_numeric_dtype(df[c])]
        candidate_time = None
        for c in numeric_cols:
            arr = df[c].dropna().values
            if len(arr) < 2:
                continue
            if np.all(np.diff(arr) >= -1e-8) or np.mean(np.diff(arr)) > 0:
                if arr[0] <= np.percentile(arr, 10) and arr[-1] > arr[0]:
                    candidate_time = c
                    break
        if not time_col:
            time_col = candidate_time
        
        candidate_v = None
        for c in numeric_cols:
            if c == time_col:
                continue
            arr = df[c].dropna().values
            if len(arr) == 0:
                continue
            rng = np.nanmax(arr) - np.nanmin(arr)
            if rng > 20 or (-120 < np.nanmin(arr) < 60 and -120 < np.nanmax(arr) < 200):
                candidate_v = c
                break
        if not voltage_col:
            voltage_col = candidate_v
    
    return time_col, voltage_col


def detect_species_from_filename(filename):
    """Detect species from filename patterns"""
    filename_lower = filename.lower()
    
    if 'rabbit' in filename_lower or 'rab' in filename_lower:
        return 'rabbit'
    elif 'mouse' in filename_lower or 'mus' in filename_lower or 'mice' in filename_lower:
        return 'mouse'
    elif 'zebrafish' in filename_lower or 'zebra' in filename_lower or 'zf' in filename_lower:
        return 'zebrafish'
    elif 'cardioid' in filename_lower or 'hps' in filename_lower or 'stem' in filename_lower:
        return 'cardioid'
    else:
        return 'default'


def detect_voltage_range_enhanced(voltage, species='default', filter_outliers=True):
    """Enhanced voltage range detection"""
    if len(voltage) == 0:
        return SPECIES_PARAMS[species]['default_y_range']
    
    voltage_clean = voltage[~np.isnan(voltage)]
    
    if len(voltage_clean) == 0:
        return SPECIES_PARAMS[species]['default_y_range']
    
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    default_range = species_params['default_y_range']
    
    if filter_outliers:
        q1 = np.percentile(voltage_clean, 25)
        q3 = np.percentile(voltage_clean, 75)
        iqr = q3 - q1
        
        lower_bound = q1 - 3 * iqr
        upper_bound = q3 + 3 * iqr
        
        filtered_voltage = voltage_clean[(voltage_clean >= lower_bound) & (voltage_clean <= upper_bound)]
        
        if len(filtered_voltage) > 10:
            v_min = np.min(filtered_voltage)
            v_max = np.max(filtered_voltage)
        else:
            v_min = np.percentile(voltage_clean, 1)
            v_max = np.percentile(voltage_clean, 99)
    else:
        v_min = np.percentile(voltage_clean, 1)
        v_max = np.percentile(voltage_clean, 99)
    
    data_range = v_max - v_min
    
    if data_range > 500:
        hist, bin_edges = np.histogram(voltage_clean, bins=100)
        max_bin_idx = np.argmax(hist)
        common_min = bin_edges[max_bin_idx]
        common_max = bin_edges[max_bin_idx + 1]
        
        expected_min, expected_max = default_range
        if common_min < expected_min - 20 or common_max > expected_max + 20:
            return default_range
        
        y_margin = max(20, (common_max - common_min) * 0.5)
        y_min = max(default_range[0], common_min - y_margin)
        y_max = min(default_range[1], common_max + y_margin)
    
    elif data_range > 200:
        margin = data_range * 0.2
        y_min = max(default_range[0], v_min - margin)
        y_max = min(default_range[1], v_max + margin)
    
    elif data_range > 50:
        y_min = max(default_range[0], v_min - 20)
        y_max = min(default_range[1], v_max + 20)
    
    else:
        y_min = max(default_range[0], v_min - 10)
        y_max = min(default_range[1], v_max + 10)
    
    if y_max - y_min < 50:
        center = (y_min + y_max) / 2
        y_min = center - 25
        y_max = center + 25
    
    return float(y_min), float(y_max)


def filter_voltage_outliers(voltage, y_min, y_max):
    """Filter voltage trace to exclude points outside specified y-range"""
    voltage_filtered = voltage.copy()
    out_of_range = (voltage < y_min) | (voltage > y_max)
    voltage_filtered[out_of_range] = np.nan
    
    n_outliers = np.sum(out_of_range)
    n_total = len(voltage)
    outlier_percentage = (n_outliers / n_total * 100) if n_total > 0 else 0
    
    return voltage_filtered, n_outliers, outlier_percentage


def read_abf_file(file_path, selected_ranges=None):
    """Read ABF file and return time and voltage arrays for selected ranges"""
    if not ABF_AVAILABLE:
        raise ImportError("pyabf not available for ABF file support")
    
    abf = pyabf.ABF(file_path)
    time_ms = abf.sweepX * 1000
    
    all_sweeps = []
    
    if abf.sweepCount > 1:
        if selected_ranges:
            sweep_numbers = []
            for range_info in selected_ranges:
                start_idx, end_idx = range_info['range']
                start_idx = max(0, start_idx)
                end_idx = min(end_idx, abf.sweepCount - 1)
                sweep_numbers.extend(range(start_idx, end_idx + 1))
        else:
            sweep_numbers = range(abf.sweepCount)
        
        sweep_numbers = sorted(set(sweep_numbers))
        
        for sweep_number in sweep_numbers:
            abf.setSweep(sweep_number)
            voltage = abf.sweepY.copy()
            
            range_name = "Unknown"
            range_description = ""
            drug = "None"
            concentration = ""
            
            if selected_ranges:
                for range_info in selected_ranges:
                    start_idx, end_idx = range_info['range']
                    if start_idx <= sweep_number <= end_idx:
                        range_name = range_info.get('name', f"Range_{start_idx + 1}-{end_idx + 1}")
                        range_description = range_info.get('description', '')
                        drug = range_info.get('drug', 'None')
                        concentration = range_info.get('concentration', '')
                        break
            
            all_sweeps.append({
                'sweep_number': sweep_number,
                'time': time_ms.copy(),
                'voltage': voltage,
                'range_name': range_name,
                'range_description': range_description,
                'drug': drug,
                'concentration': concentration
            })
    else:
        abf.setSweep(0)
        voltage = abf.sweepY
        all_sweeps.append({
            'sweep_number': 0,
            'time': time_ms,
            'voltage': voltage,
            'range_name': 'Single',
            'range_description': 'Single sweep',
            'drug': 'None',
            'concentration': ''
        })
    
    return all_sweeps


def extract_metadata_from_filename(filename):
    """Extract Cell_ID and Frequency from filename"""
    filename_lower = filename.lower()
    
    freq_patterns = [
        r'(\d+\.?\d*)\s*hz',
        r'(\d+\.?\d*)hz',
        r'freq[_\-\s]*(\d+\.?\d*)',
        r'(\d+\.?\d*)\s*Hz'
    ]
    
    frequency = None
    for pattern in freq_patterns:
        match = re.search(pattern, filename_lower)
        if match:
            freq_val = match.group(1)
            if freq_val in ['0.5', '0.5Hz', '0.5 Hz']:
                frequency = '0.5'
            elif freq_val in ['1', '1.0', '1Hz', '1 Hz']:
                frequency = '1.0'
            elif freq_val in ['2', '2.0', '2Hz', '2 Hz']:
                frequency = '2.0'
            elif freq_val in ['3', '3.0', '3Hz', '3 Hz']:
                frequency = '3.0'
            else:
                frequency = freq_val
            break
    
    cell_patterns = [
        r'cell[_\-\s]*([a-zA-Z0-9]+)',
        r'c([a-zA-Z0-9]+)',
        r'([a-zA-Z0-9]+)[_\-\s]*\d+\.?\d*hz'
    ]
    
    cell_id = None
    for pattern in cell_patterns:
        match = re.search(pattern, filename_lower)
        if match:
            cell_id = f"Cell_{match.group(1)}"
            break
    
    if cell_id is None:
        cell_id = f"Cell_{Path(filename).stem}"
    
    return cell_id, frequency


def smooth_voltage(voltage, method='savgol', window_ms=3.0, dt_ms=None):
    """Smooth voltage trace"""
    if dt_ms is None or len(voltage) < 5:
        return voltage
    window_samples = max(3, int(round(window_ms / dt_ms)))
    if window_samples % 2 == 0:
        window_samples += 1
    if method == 'savgol' and window_samples >= 5:
        try:
            polyorder = min(3, window_samples - 1)
            return savgol_filter(voltage, window_length=window_samples, polyorder=polyorder, mode='nearest')
        except Exception:
            return gaussian_filter1d(voltage, sigma=1)
    else:
        sigma = max(1, window_samples / 3.0)
        return gaussian_filter1d(voltage, sigma=sigma)


def calculate_rmp(voltage, time, baseline_window_ms=50):
    """Estimate resting membrane potential"""
    dt = time[1] - time[0]
    n = int(round(baseline_window_ms / dt))
    if n < 1:
        n = 1
    return float(np.nanmean(voltage[:n]))


def dual_path_peak_detection(time, voltage_raw, voltage_smooth, dt_ms, species='default'):
    """Dual-path peak detection"""
    if len(time) < 10:
        return np.array([]), np.array([]), np.array([])
    
    peaks_raw, properties_raw = find_peaks(
        voltage_raw,
        prominence=SPECIES_PARAMS[species]['min_peak_prominence'],
        distance=int(2 / dt_ms) if dt_ms > 0 else 10,
        height=np.nanmax(voltage_raw) * 0.3
    )
    
    peaks_smooth, properties_smooth = find_peaks(
        voltage_smooth,
        prominence=SPECIES_PARAMS[species]['min_peak_prominence'] * 0.8,
        distance=int(2 / dt_ms) if dt_ms > 0 else 10,
        height=np.nanmax(voltage_smooth) * 0.3
    )
    
    final_peaks = []
    
    for peak in peaks_raw:
        if any(abs(peak - p_smooth) <= 5 for p_smooth in peaks_smooth):
            final_peaks.append(peak)
    
    if len(final_peaks) < 5 and len(peaks_smooth) > 0:
        smooth_peaks_sorted = sorted(peaks_smooth, key=lambda x: voltage_smooth[x], reverse=True)
        for peak in smooth_peaks_sorted:
            if len(final_peaks) >= 5:
                break
            if not any(abs(peak - p) <= 5 for p in final_peaks):
                final_peaks.append(peak)
    
    final_peaks = sorted(final_peaks)
    
    return np.array(final_peaks), peaks_raw, peaks_smooth


def calculate_stv(apd_values):
    """Calculate Short-Term Variability for APD values"""
    if len(apd_values) < 5:
        return np.nan, "Insufficient data (minimum 5 beats required)"
    
    try:
        apd_clean = [v for v in apd_values if not math.isnan(v)]
        
        if len(apd_clean) < 5:
            return np.nan, f"Insufficient valid data ({len(apd_clean)} beats)"
        
        differences = np.abs(np.diff(apd_clean))
        stv = np.sum(differences) / (len(apd_clean) * math.sqrt(2))
        
        mean_apd = np.mean(apd_clean)
        sd_apd = np.std(apd_clean)
        cv_apd = (sd_apd / mean_apd) * 100 if mean_apd != 0 else np.nan
        
        note = f"Based on {len(apd_clean)} beats, mean APD: {mean_apd:.1f} ms, CV: {cv_apd:.1f}%"
        
        return float(stv), note
    
    except (ZeroDivisionError, ValueError, TypeError) as e:
        return np.nan, f"Calculation error: {str(e)}"


def distinguish_stimulation_vs_ap(time, voltage, dt_ms, stim_search_height=50, stim_prominence=80,
                                  stim_width_max_ms=2.0, min_apd90_ms=50.0, debug=False,
                                  use_biological_peak_detection=False, species='default',
                                  immature_mode=False):
    """Distinguish between stimulation artifacts and biological APs"""
    res = {}
    
    # For cardioid immature mode, use more aggressive artifact rejection
    if species == 'cardioid' and immature_mode:
        # Lower thresholds for artifact detection
        stim_search_height = 20
        stim_prominence = 25
        # Wider search window for biological APs
        search_window_ms = 500
        # Minimum distance from artifact to biological AP
        min_artifact_distance_ms = 30
        # CRITICAL: Minimum time after stimulation to look for real APs (ms)
        # This skips the stimulation artifact region entirely
        min_ap_time_ms = 25  # Don't look for APs until at least 25ms after stimulation
    else:
        search_window_ms = 300
        min_artifact_distance_ms = 5
        min_ap_time_ms = 5
    
    # Find stimulation artifacts (very sharp, narrow peaks)
    stim_peaks, stim_props = signal.find_peaks(voltage, height=stim_search_height,
                                               prominence=stim_prominence,
                                               width=(0, int(round(stim_width_max_ms / dt_ms))))
    
    stim_times_ms = [float(time[i]) for i in stim_peaks]
    res['stim_times_idx'] = stim_peaks
    res['stim_times_ms'] = stim_times_ms
    
    # Find all candidate peaks (including biological APs)
    all_peaks, all_props = signal.find_peaks(voltage, 
                                             prominence=np.std(voltage) * 0.2,  # Lower threshold
                                             distance=int(round(5.0 / dt_ms)))  # Smaller minimum distance
    
    # CRITICAL FIX: Remove any peaks that occur too early after stimulation
    # This MUST happen BEFORE any other validation
    filtered_peaks = []
    for p in all_peaks:
        # Check if this peak is too close to any stimulation artifact
        is_too_early = False
        for stim_idx in stim_peaks:
            time_diff_ms = (p - stim_idx) * dt_ms
            if 0 <= time_diff_ms < min_ap_time_ms:
                is_too_early = True
                break
        if not is_too_early:
            filtered_peaks.append(p)
    
    all_peaks = filtered_peaks
    res['all_candidate_peaks_idx'] = all_peaks
    
    real_peaks = []
    
    # First, identify and reject stimulation artifacts based on width and shape
    artifact_candidates = []
    for p in all_peaks:
        # Check width at half height
        try:
            peak_height = voltage[p]
            # Find baseline for this peak
            baseline_start = max(0, p - int(20 / dt_ms))
            baseline_median = np.median(voltage[baseline_start:p])
            half_height = baseline_median + (peak_height - baseline_median) / 2
            left_idx = p
            right_idx = p
            while left_idx > max(0, p-30) and voltage[left_idx] > half_height:
                left_idx -= 1
            while right_idx < min(len(voltage)-1, p+30) and voltage[right_idx] > half_height:
                right_idx += 1
            width_samples = right_idx - left_idx
            width_ms = width_samples * dt_ms
            
            # Artifacts are very narrow (< 2ms)
            if width_ms < 2.0:
                artifact_candidates.append(p)
        except:
            pass
    
    # For cardioid immature mode, also check peak prominence and height ratio
    if species == 'cardioid' and immature_mode:
        # Calculate median voltage in baseline
        baseline_median = np.median(voltage[:min(100, len(voltage))])
        
        for p in all_peaks:
            # Check if this is likely an artifact (very high, very narrow)
            is_artifact = False
            
            # Artifacts are often > 50mV above baseline
            if voltage[p] - baseline_median > 50:
                # Check width
                is_artifact = p in artifact_candidates
            
            # Also check if there's a larger peak nearby (the real AP is often smaller!)
            nearby_peaks = [pp for pp in all_peaks if abs(pp - p) < int(50/dt_ms) and pp != p]
            if nearby_peaks:
                # If this peak is much larger than nearby peaks, it's likely artifact
                if voltage[p] > max(voltage[pp] for pp in nearby_peaks) * 1.5:
                    is_artifact = True
            
            if not is_artifact:
                real_peaks.append(p)
    else:
        real_peaks = [p for p in all_peaks if p not in artifact_candidates]
    
    # For each stimulation artifact, look for a biological AP after it
    for stim_idx in stim_peaks:
        min_distance_samples = int(round(min_artifact_distance_ms / dt_ms))
        search_start = stim_idx + min_distance_samples
        search_end = stim_idx + int(round(search_window_ms / dt_ms))
        search_end = min(search_end, len(voltage) - 1)
        
        if search_start >= search_end:
            continue
        
        # Find peaks in this window that are NOT artifacts and not too early
        cands = [p for p in real_peaks if search_start <= p <= search_end]
        
        if cands:
            best_peak = None
            best_score = -1
            
            for p in cands:
                try:
                    baseline_window = max(0, p - int(100 / dt_ms))
                    baseline_voltage = voltage[baseline_window:p]
                    if len(baseline_voltage) > 0:
                        rmp_estimate = np.median(baseline_voltage)
                    else:
                        rmp_estimate = np.median(voltage[:min(100, len(voltage))])
                    
                    apa_estimate = voltage[p] - rmp_estimate
                    
                    # Look for repolarization
                    repolarization_found = False
                    search_repol_end = min(len(voltage), p + int(300 / dt_ms))
                    target_v = rmp_estimate + 0.1 * apa_estimate if apa_estimate > 0 else rmp_estimate
                    for i in range(p + 1, search_repol_end):
                        if voltage[i] <= target_v:
                            repolarization_found = True
                            break
                    
                    # Score based on APA and repolarization
                    score = 0
                    if apa_estimate > 10:
                        score += 1
                    if repolarization_found:
                        score += 2
                    if apa_estimate > 30:
                        score += 1
                    
                    if score > best_score:
                        best_score = score
                        best_peak = p
                        
                except Exception as e:
                    continue
            
            if best_peak is not None and best_score >= 1:
                if best_peak not in real_peaks:
                    real_peaks.append(best_peak)
    
    # Remove duplicates and sort
    real_peaks = sorted(list(set(real_peaks)))
    
    # Final validation: ensure peaks have reasonable APD and are not artifacts
    valid_peaks = []
    for p in real_peaks:
        try:
            baseline_window = max(0, p - int(50 / dt_ms))
            baseline_voltage = voltage[baseline_window:p]
            if len(baseline_voltage) > 0:
                rmp_temp = np.median(baseline_voltage)
            else:
                rmp_temp = np.median(voltage[:min(100, len(voltage))])
            
            peak_v = voltage[p]
            apa_temp = peak_v - rmp_temp
            
            # Check if this looks like a real AP (not artifact)
            if apa_temp > 10:
                # Check for repolarization
                repolarization_found = False
                search_end = min(len(voltage), p + int(300 / dt_ms))
                target_v = rmp_temp + 0.1 * apa_temp
                for i in range(p + 1, search_end):
                    if voltage[i] <= target_v:
                        repolarization_found = True
                        break
                
                if repolarization_found:
                    valid_peaks.append(p)
                elif species == 'cardioid' and immature_mode:
                    # In immature mode, be more permissive
                    valid_peaks.append(p)
                    
        except Exception:
            continue
    
    res['real_ap_peaks_idx'] = np.array(valid_peaks, dtype=int)
    
    # Debug output
    if debug or len(valid_peaks) == 0:
        print(f"Cardioid Detection (immature={immature_mode}): {len(stim_peaks)} stimulation artifacts, "
              f"{len(all_peaks)} total peaks (after filtering early peaks), {len(valid_peaks)} valid APs, "
              f"{len(artifact_candidates)} artifact candidates")
        if len(valid_peaks) == 0 and species == 'cardioid' and immature_mode:
            print(f"  No APs detected automatically. Using manual selection will work.")
    
    return res


def find_biological_peak_after_stimulus(time, voltage, stim_idx, dt_ms, min_apd90_ms=50.0, species='default'):
    """Find biological AP peak after stimulation artifact"""
    if stim_idx >= len(voltage) - 10:
        return None
    
    species_params = SPECIES_PARAMS.get(species, SPECIES_PARAMS['default'])
    min_peak_prominence = species_params['min_peak_prominence']
    
    search_start = stim_idx + max(1, int(round(2.0 / dt_ms)))
    search_end = stim_idx + int(round(300.0 / dt_ms))
    search_end = min(search_end, len(voltage) - 1)
    
    if search_start >= search_end:
        return None
    
    search_voltage = voltage[search_start:search_end]
    search_time = time[search_start:search_end]
    
    if len(search_voltage) < 10:
        return None
    
    try:
        peaks, properties = signal.find_peaks(
            search_voltage,
            height=np.nanmax(search_voltage) * 0.3,
            prominence=min_peak_prominence,
            width=int(round(1.0 / dt_ms)),
            distance=int(round(10.0 / dt_ms))
        )
        
        if len(peaks) == 0:
            return None
        
        absolute_peaks = [search_start + p for p in peaks]
        
        valid_peaks = []
        for peak_idx in absolute_peaks:
            try:
                metrics = compute_apd_metrics_enhanced_v3(time, voltage, peak_idx, species=species)
                
                if species == 'zebrafish' or species == 'cardioid':
                    if (metrics['APD90'] >= min_apd90_ms * 0.7 and
                            metrics['dVdt_max'] > 5 and
                            metrics['APA'] > 15):
                        valid_peaks.append(peak_idx)
                else:
                    if (metrics['APD90'] >= min_apd90_ms and
                            metrics['dVdt_max'] > 10 and
                            metrics['APA'] > 20):
                        valid_peaks.append(peak_idx)
            except Exception:
                continue
        
        if valid_peaks:
            min_distance_from_stim = int(round(5.0 / dt_ms))
            far_peaks = [p for p in valid_peaks if p > stim_idx + min_distance_from_stim]
            
            if far_peaks:
                return max(far_peaks, key=lambda p: voltage[p])
            else:
                return valid_peaks[0]
        else:
            return None
    
    except Exception as e:
        print(f"Biological peak detection error: {e}")
        return None


# ============================================================================
# Universal Metadata Editor
# ============================================================================

class UniversalMetadataEditor(tk.Toplevel):
    """Universal metadata editor for all file types with click-and-drag selection"""
    
    def __init__(self, parent, file_metadata, all_results=None):
        super().__init__(parent)
        self.parent = parent
        self.file_metadata = file_metadata
        self.all_results = all_results or []
        self.modified_metadata = {}
        
        self.title("APEX - Universal Metadata Editor")
        self.geometry("700x600")
        self.transient(parent)
        self.grab_set()
        
        self.configure(bg='white')
        
        self.selection_start = None
        self.selection_mode = False
        
        header = ttk.Label(self, text="Edit Metadata for All File Types",
                           font=("Helvetica", 12, "bold"), background='white')
        header.pack(pady=10)
        
        main_frame = ttk.Frame(self)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        canvas = tk.Canvas(main_frame)
        scrollbar = ttk.Scrollbar(main_frame, orient=tk.VERTICAL, command=canvas.yview)
        self.scrollable_frame = ttk.Frame(canvas)
        
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.create_metadata_controls()
        
        button_frame = ttk.Frame(self)
        button_frame.pack(pady=10)
        
        ttk.Button(button_frame, text="Apply Changes", command=self.apply_metadata, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=self.cancel, width=15).pack(side=tk.LEFT, padx=5)
    
    def create_metadata_controls(self):
        """Create metadata editing controls with drag selection"""
        file_frame = ttk.LabelFrame(self.scrollable_frame, text="Select Files to Edit", padding=10)
        file_frame.pack(fill=tk.X, pady=10)
        
        select_all_frame = ttk.Frame(file_frame)
        select_all_frame.pack(fill=tk.X, pady=5)
        ttk.Button(select_all_frame, text="Select All", 
                   command=self.select_all_files, width=12).pack(side=tk.LEFT, padx=5)
        ttk.Button(select_all_frame, text="Clear Selection", 
                   command=self.clear_selection, width=12).pack(side=tk.LEFT, padx=5)
        
        columns = ("Select", "File", "Type", "Cell ID", "Frequency", "Drug", "Sweeps")
        self.file_tree = ttk.Treeview(file_frame, columns=columns, show='headings', height=8)
        
        for col in columns:
            self.file_tree.heading(col, text=col)
            self.file_tree.column(col, width=100)
        
        tree_scroll = ttk.Scrollbar(file_frame, orient=tk.VERTICAL, command=self.file_tree.yview)
        self.file_tree.configure(yscrollcommand=tree_scroll.set)
        
        self.file_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.file_tree.bind('<ButtonPress-1>', self.on_select_start)
        self.file_tree.bind('<B1-Motion>', self.on_select_drag)
        self.file_tree.bind('<ButtonRelease-1>', self.on_select_end)
        
        self.populate_file_list()
        
        meta_frame = ttk.LabelFrame(self.scrollable_frame, text="Edit Metadata", padding=10)
        meta_frame.pack(fill=tk.X, pady=10)
        
        cell_frame = ttk.Frame(meta_frame)
        cell_frame.pack(fill=tk.X, pady=5)
        ttk.Label(cell_frame, text="Cell ID:").pack(side=tk.LEFT, padx=5)
        self.cell_id_var = tk.StringVar()
        ttk.Entry(cell_frame, textvariable=self.cell_id_var, width=30).pack(side=tk.LEFT, padx=5)
        
        freq_frame = ttk.Frame(meta_frame)
        freq_frame.pack(fill=tk.X, pady=5)
        ttk.Label(freq_frame, text="Frequency (Hz):").pack(side=tk.LEFT, padx=5)
        self.frequency_var = tk.StringVar()
        freq_combo = ttk.Combobox(freq_frame, textvariable=self.frequency_var,
                                  values=['0.5', '1.0', '2.0', '3.0', '4.0', '5.0', 'Unknown'],
                                  state="normal", width=20)
        freq_combo.pack(side=tk.LEFT, padx=5)
        
        drug_frame = ttk.Frame(meta_frame)
        drug_frame.pack(fill=tk.X, pady=5)
        ttk.Label(drug_frame, text="Drug/Condition:").pack(side=tk.LEFT, padx=5)
        self.drug_var = tk.StringVar(value="None")
        drug_combo = ttk.Combobox(drug_frame, textvariable=self.drug_var,
                                  values=COMMON_DRUGS, state="readonly", width=20)
        drug_combo.pack(side=tk.LEFT, padx=5)
        
        conc_frame = ttk.Frame(meta_frame)
        conc_frame.pack(fill=tk.X, pady=5)
        ttk.Label(conc_frame, text="Concentration:").pack(side=tk.LEFT, padx=5)
        self.concentration_var = tk.StringVar()
        ttk.Entry(conc_frame, textvariable=self.concentration_var, width=30).pack(side=tk.LEFT, padx=5)
        
        species_frame = ttk.Frame(meta_frame)
        species_frame.pack(fill=tk.X, pady=5)
        ttk.Label(species_frame, text="Species:").pack(side=tk.LEFT, padx=5)
        self.species_var = tk.StringVar(value="auto")
        species_combo = ttk.Combobox(species_frame, textvariable=self.species_var,
                                     values=["auto", "rabbit", "mouse", "zebrafish", "cardioid", "default"],
                                     state="readonly", width=20)
        species_combo.pack(side=tk.LEFT, padx=5)
        
        batch_frame = ttk.Frame(meta_frame)
        batch_frame.pack(fill=tk.X, pady=10)
        ttk.Label(batch_frame, text="Apply to:").pack(side=tk.LEFT, padx=5)
        self.apply_to_var = tk.StringVar(value="selected")
        ttk.Radiobutton(batch_frame, text="Selected files", variable=self.apply_to_var, value="selected").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(batch_frame, text="All files", variable=self.apply_to_var, value="all").pack(side=tk.LEFT, padx=5)
        
        preview_frame = ttk.LabelFrame(self.scrollable_frame, text="Preview", padding=10)
        preview_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        self.preview_text = scrolledtext.ScrolledText(preview_frame, height=8, width=80)
        self.preview_text.pack(fill=tk.BOTH, expand=True)
        
        ttk.Button(preview_frame, text="Update Preview", command=self.update_preview, width=15).pack(pady=5)
    
    def populate_file_list(self):
        """Populate file list with all loaded files"""
        for file_path, metadata in self.file_metadata.items():
            filename = Path(file_path).name
            file_type = "ABF" if file_path.endswith('.abf') else "CSV/Excel"
            cell_id = metadata.get('cell_id', 'Unknown')
            frequency = metadata.get('frequency', 'Unknown')
            drug = metadata.get('drug', 'None')
            
            sweeps = ""
            if file_path.endswith('.abf'):
                sweeps = metadata.get('sweep_count', '1')
            
            self.file_tree.insert('', tk.END, values=(
                "",
                filename,
                file_type,
                cell_id,
                frequency,
                drug,
                sweeps
            ))
    
    def on_select_start(self, event):
        self.selection_start = self.file_tree.identify_row(event.y)
        if self.selection_start:
            self.file_tree.selection_set(self.selection_start)
            self.selection_mode = True
    
    def on_select_drag(self, event):
        if self.selection_mode and self.selection_start:
            current_item = self.file_tree.identify_row(event.y)
            if current_item:
                all_items = self.file_tree.get_children()
                if self.selection_start in all_items and current_item in all_items:
                    start_idx = all_items.index(self.selection_start)
                    current_idx = all_items.index(current_item)
                    
                    if start_idx <= current_idx:
                        items_to_select = all_items[start_idx:current_idx + 1]
                    else:
                        items_to_select = all_items[current_idx:start_idx + 1]
                    
                    self.file_tree.selection_set(items_to_select)
    
    def on_select_end(self, event):
        self.selection_mode = False
        self.selection_start = None
    
    def select_all_files(self):
        all_items = self.file_tree.get_children()
        if all_items:
            self.file_tree.selection_set(all_items)
    
    def clear_selection(self):
        self.file_tree.selection_remove(self.file_tree.selection())
    
    def update_preview(self):
        self.preview_text.delete(1.0, tk.END)
        
        selected_items = self.file_tree.selection()
        apply_to_all = (self.apply_to_var.get() == "all")
        
        files_to_update = []
        
        if apply_to_all:
            files_to_update = list(self.file_metadata.keys())
        elif selected_items:
            for item in selected_items:
                values = self.file_tree.item(item)['values']
                if values:
                    filename = values[1]
                    for file_path in self.file_metadata.keys():
                        if Path(file_path).name == filename:
                            files_to_update.append(file_path)
                            break
        
        if not files_to_update:
            self.preview_text.insert(tk.END, "No files selected for update.\n")
            return
        
        cell_id = self.cell_id_var.get()
        frequency = self.frequency_var.get()
        drug = self.drug_var.get()
        concentration = self.concentration_var.get()
        species = self.species_var.get()
        
        self.preview_text.insert(tk.END, f"Will update {len(files_to_update)} files:\n")
        self.preview_text.insert(tk.END, "=" * 50 + "\n\n")
        
        for i, file_path in enumerate(files_to_update[:10]):
            current_meta = self.file_metadata[file_path]
            
            new_cell = cell_id if cell_id else current_meta.get('cell_id', '')
            new_freq = frequency if frequency else current_meta.get('frequency', '')
            new_drug = drug if drug else current_meta.get('drug', '')
            new_conc = concentration if concentration else current_meta.get('concentration', '')
            new_species = species if species != 'auto' else current_meta.get('species', '')
            
            self.preview_text.insert(tk.END,
                                     f"{Path(file_path).name}\n"
                                     f"  Cell ID: {current_meta.get('cell_id', '')} → {new_cell}\n"
                                     f"  Frequency: {current_meta.get('frequency', '')} → {new_freq}\n"
                                     f"  Drug: {current_meta.get('drug', '')} → {new_drug}\n"
                                     f"  Species: {current_meta.get('species', '')} → {new_species}\n\n")
        
        if len(files_to_update) > 10:
            self.preview_text.insert(tk.END, f"\n... and {len(files_to_update) - 10} more files")
    
    def apply_metadata(self):
        selected_items = self.file_tree.selection()
        apply_to_all = (self.apply_to_var.get() == "all")
        
        files_to_update = []
        
        if apply_to_all:
            files_to_update = list(self.file_metadata.keys())
        elif selected_items:
            for item in selected_items:
                values = self.file_tree.item(item)['values']
                if values:
                    filename = values[1]
                    for file_path in self.file_metadata.keys():
                        if Path(file_path).name == filename:
                            files_to_update.append(file_path)
                            break
        
        if not files_to_update:
            messagebox.showwarning("No Selection", "Please select files to update")
            return
        
        cell_id = self.cell_id_var.get()
        frequency = self.frequency_var.get()
        drug = self.drug_var.get()
        concentration = self.concentration_var.get()
        species = self.species_var.get()
        
        for file_path in files_to_update:
            meta = self.file_metadata[file_path]
            
            original = meta.copy()
            
            if cell_id:
                meta['cell_id'] = cell_id
                meta['display_cell_id'] = cell_id
            
            if frequency and frequency != 'Unknown':
                meta['frequency'] = frequency
            
            if drug:
                meta['drug'] = drug
            
            if concentration:
                meta['concentration'] = concentration
            
            if species and species != 'auto':
                meta['species'] = species
            
            self.modified_metadata[file_path] = {
                'original': original,
                'modified': meta.copy()
            }
        
        messagebox.showinfo("Metadata Updated",
                            f"Updated metadata for {len(files_to_update)} files")
        
        self.destroy()
    
    def cancel(self):
        self.modified_metadata = None
        self.destroy()
    
    def get_modified_metadata(self):
        return self.modified_metadata


# ============================================================================
# Collapsible Panel System for GUI
# ============================================================================

class CollapsiblePanel(ttk.Frame):
    """Collapsible panel with title and content"""
    
    def __init__(self, parent, title, *args, **kwargs):
        ttk.Frame.__init__(self, parent, *args, **kwargs)
        
        self.title = title
        self.is_expanded = True
        
        self.title_frame = ttk.Frame(self)
        self.title_frame.pack(fill=tk.X, pady=(0, 5))
        
        self.toggle_btn = ttk.Button(self.title_frame, text="▼ " + title,
                                     command=self.toggle, width=20)
        self.toggle_btn.pack(side=tk.LEFT)
        
        ttk.Separator(self.title_frame, orient='horizontal').pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        
        self.content_frame = ttk.Frame(self)
        self.content_frame.pack(fill=tk.X, padx=10)
    
    def toggle(self):
        if self.is_expanded:
            self.content_frame.pack_forget()
            self.toggle_btn.config(text="▶ " + self.title)
        else:
            self.content_frame.pack(fill=tk.X, padx=10)
            self.toggle_btn.config(text="▼ " + self.title)
        
        self.is_expanded = not self.is_expanded
    
    def add_widget(self, widget, **pack_args):
        widget.pack(in_=self.content_frame, **pack_args)


# ============================================================================
# Rejection Manager
# ============================================================================

class RejectionManager:
    def __init__(self):
        self.rejected_traces = []
        self.rejection_reasons = {}
    
    def reject_trace(self, trace_id, reason="User rejected"):
        if trace_id not in self.rejected_traces:
            self.rejected_traces.append(trace_id)
            self.rejection_reasons[trace_id] = reason
    
    def undo_rejection(self, trace_id):
        if trace_id in self.rejected_traces:
            self.rejected_traces.remove(trace_id)
            if trace_id in self.rejection_reasons:
                del self.rejection_reasons[trace_id]
    
    def is_rejected(self, trace_id):
        return trace_id in self.rejected_traces
    
    def get_rejection_summary(self):
        return self.rejected_traces.copy(), self.rejection_reasons.copy()
    
    def get_reason(self, trace_id):
        return self.rejection_reasons.get(trace_id, "No reason provided")


# ============================================================================
# Enhanced APEX Platform - Main Class
# ============================================================================

class APEXPlatformEnhanced:
    def __init__(self, root):
        self.root = root
        self.root.title("APEX - Professional Cardiac Electrophysiology Platform ©VkV2025")
        
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        window_width = int(screen_width * 0.9)
        window_height = int(screen_height * 0.9)
        self.root.geometry(f"{window_width}x{window_height}")
        
        x_position = (screen_width - window_width) // 2
        y_position = (screen_height - window_height) // 2
        self.root.geometry(f"+{x_position}+{y_position}")
        
        self.file_list = []
        self.parsed_files = {}
        self.output_folder = Path.cwd() / "APEX_Professional_Output"
        self.all_results = []
        self.current_trace_index = 0
        self.validated_flags = {}
        self.all_files_validated = False
        
        self.rejection_manager = RejectionManager()
        
        self.smoothing = tk.BooleanVar(value=True)
        self.smooth_method = tk.StringVar(value='savgol')
        # Fix for empty smoothing_ms - use StringVar instead of DoubleVar
        self.smoothing_ms = tk.StringVar(value="")
        self.min_apd90 = tk.DoubleVar(value=50.0)
        
        self.file_metadata = {}
        
        self.use_biological_detection = tk.BooleanVar(value=False)
        self.use_corrected_apd = tk.BooleanVar(value=True)
        
        self.abf_trace_selections = {}
        
        self.manual_peak_corrections = {}
        self.manual_upstroke_corrections = {}
        self.late_repolarization_corrections = {}
        
        self.interactive_selector = None
        self.upstroke_selector = None
        
        self.yaxis_auto = tk.BooleanVar(value=True)
        self.yaxis_min = tk.DoubleVar(value=-90)
        self.yaxis_max = tk.DoubleVar(value=80)
        self.filter_outliers = tk.BooleanVar(value=True)
        self.visual_filter_only = tk.BooleanVar(value=True)
        
        self.species_detection = tk.BooleanVar(value=True)
        self.selected_species = tk.StringVar(value="auto")
        
        self.sync_zoom = tk.BooleanVar(value=False)
        self.current_xlim = None
        self.current_ylim = None
        
        self.use_dual_path_detection = tk.BooleanVar(value=True)
        
        self.stacked_files = {}
        
        self.validated_traces = set()
        
        # CHANGE 2: Add cardioid immature mode setting
        self.cardioid_immature_mode = tk.BooleanVar(value=False)
        
        self.export_settings = {
            'ap_parameter_matrix': tk.BooleanVar(value=True),
            'raw_ap_data': tk.BooleanVar(value=True),
            'frequency_drug_response': tk.BooleanVar(value=True),
            'comprehensive_analysis': tk.BooleanVar(value=True),
            'individual_traces': tk.BooleanVar(value=True),
            'average_traces': tk.BooleanVar(value=True),
            'ap_overlay_raw': tk.BooleanVar(value=False),
            'average_ap_sem': tk.BooleanVar(value=False),
            'drug_comparison': tk.BooleanVar(value=False),
            'frequency_comparison': tk.BooleanVar(value=False),
            'stv_analysis': tk.BooleanVar(value=True),
            'normalized_ap': tk.BooleanVar(value=False),
            'one_figure_per_cell': tk.BooleanVar(value=False)
        }
        
        # Track analyzed traces for incremental analysis
        self.analyzed_trace_ids = set()
        
        self.build_enhanced_ui()
        
        self.selected_species.trace_add('write', self.on_species_change)
        
        # Load saved settings
        self.load_settings()
        
        # Bind window close event to save settings
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
    
    def load_settings(self):
        """Load saved user settings"""
        config = load_config()
        
        # Apply loaded settings
        self.selected_species.set(config.get('selected_species', 'auto'))
        self.yaxis_auto.set(config.get('yaxis_auto', True))
        self.yaxis_min.set(config.get('yaxis_min', -90.0))
        self.yaxis_max.set(config.get('yaxis_max', 80.0))
        self.smoothing.set(config.get('smoothing', True))
        self.smoothing_ms.set(config.get('smoothing_ms', ''))
        self.smooth_method.set(config.get('smooth_method', 'savgol'))
        self.use_corrected_apd.set(config.get('use_corrected_apd', True))
        self.use_dual_path_detection.set(config.get('use_dual_path_detection', True))
        self.filter_outliers.set(config.get('filter_outliers', True))
        self.visual_filter_only.set(config.get('visual_filter_only', True))
        self.sync_zoom.set(config.get('sync_zoom', False))
        # CHANGE 2: Load cardioid immature mode setting
        self.cardioid_immature_mode.set(config.get('cardioid_immature_mode', False))
        
        # Load export settings
        export_config = config.get('export_settings', {})
        for key, value in export_config.items():
            if key in self.export_settings:
                self.export_settings[key].set(value)
        
        # Load output folder
        output_folder_str = config.get('output_folder', '')
        if output_folder_str and os.path.exists(output_folder_str):
            self.output_folder = Path(output_folder_str)
            self.output_label.config(text=f"{self.output_folder}")
        
        # Update UI based on loaded settings
        self.on_yaxis_auto_toggle()
    
    def save_settings(self):
        """Save current user settings"""
        config = {
            'selected_species': self.selected_species.get(),
            'yaxis_auto': self.yaxis_auto.get(),
            'yaxis_min': self.yaxis_min.get(),
            'yaxis_max': self.yaxis_max.get(),
            'smoothing': self.smoothing.get(),
            'smoothing_ms': self.smoothing_ms.get(),
            'smooth_method': self.smooth_method.get(),
            'use_corrected_apd': self.use_corrected_apd.get(),
            'use_dual_path_detection': self.use_dual_path_detection.get(),
            'filter_outliers': self.filter_outliers.get(),
            'visual_filter_only': self.visual_filter_only.get(),
            'sync_zoom': self.sync_zoom.get(),
            'output_folder': str(self.output_folder),
            'cardioid_immature_mode': self.cardioid_immature_mode.get(),
            'export_settings': {
                key: var.get() for key, var in self.export_settings.items()
            }
        }
        save_config(config)
    
    def on_closing(self):
        """Handle window closing event"""
        self.save_settings()
        if messagebox.askokcancel("Quit", "Do you want to quit APEX Platform?"):
            self.root.destroy()
    
    def save_configuration_to_file(self):
        """Save current configuration to user-selected file"""
        config = {
            'selected_species': self.selected_species.get(),
            'yaxis_auto': self.yaxis_auto.get(),
            'yaxis_min': self.yaxis_min.get(),
            'yaxis_max': self.yaxis_max.get(),
            'smoothing': self.smoothing.get(),
            'smoothing_ms': self.smoothing_ms.get(),
            'smooth_method': self.smooth_method.get(),
            'use_corrected_apd': self.use_corrected_apd.get(),
            'use_dual_path_detection': self.use_dual_path_detection.get(),
            'filter_outliers': self.filter_outliers.get(),
            'visual_filter_only': self.visual_filter_only.get(),
            'sync_zoom': self.sync_zoom.get(),
            'cardioid_immature_mode': self.cardioid_immature_mode.get(),
            'export_settings': {
                key: var.get() for key, var in self.export_settings.items()
            }
        }
        
        file_path = filedialog.asksaveasfilename(
            title="Save Configuration",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        
        if file_path:
            try:
                with open(file_path, 'w') as f:
                    json.dump(config, f, indent=2)
                messagebox.showinfo("Configuration Saved", 
                                   f"Configuration saved to:\n{file_path}")
            except Exception as e:
                messagebox.showerror("Save Error", f"Could not save configuration:\n{str(e)}")
    
    def load_configuration_from_file(self):
        """Load configuration from user-selected file"""
        file_path = filedialog.askopenfilename(
            title="Load Configuration",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        
        if file_path:
            try:
                with open(file_path, 'r') as f:
                    config = json.load(f)
                
                # Apply loaded settings
                if 'selected_species' in config:
                    self.selected_species.set(config['selected_species'])
                if 'yaxis_auto' in config:
                    self.yaxis_auto.set(config['yaxis_auto'])
                if 'yaxis_min' in config:
                    self.yaxis_min.set(config['yaxis_min'])
                if 'yaxis_max' in config:
                    self.yaxis_max.set(config['yaxis_max'])
                if 'smoothing' in config:
                    self.smoothing.set(config['smoothing'])
                if 'smoothing_ms' in config:
                    self.smoothing_ms.set(config['smoothing_ms'])
                if 'smooth_method' in config:
                    self.smooth_method.set(config['smooth_method'])
                if 'use_corrected_apd' in config:
                    self.use_corrected_apd.set(config['use_corrected_apd'])
                if 'use_dual_path_detection' in config:
                    self.use_dual_path_detection.set(config['use_dual_path_detection'])
                if 'filter_outliers' in config:
                    self.filter_outliers.set(config['filter_outliers'])
                if 'visual_filter_only' in config:
                    self.visual_filter_only.set(config['visual_filter_only'])
                if 'sync_zoom' in config:
                    self.sync_zoom.set(config['sync_zoom'])
                if 'cardioid_immature_mode' in config:
                    self.cardioid_immature_mode.set(config['cardioid_immature_mode'])
                
                # Load export settings
                if 'export_settings' in config:
                    for key, value in config['export_settings'].items():
                        if key in self.export_settings:
                            self.export_settings[key].set(value)
                
                # Update UI
                self.on_yaxis_auto_toggle()
                
                # Show message about smoothing if cardioid immature mode is enabled
                if self.cardioid_immature_mode.get():
                    self.show_immature_mode_smoothing_suggestion()
                
                # Re-plot current trace if available
                if self.all_results:
                    self.plot_current_trace()
                
                messagebox.showinfo("Configuration Loaded", 
                                   f"Configuration loaded from:\n{file_path}")
                
            except Exception as e:
                messagebox.showerror("Load Error", f"Could not load configuration:\n{str(e)}")
    
    def reset_analysis_settings(self):
        """Reset all analysis parameters to DEFAULT_CONFIG values"""
        response = messagebox.askyesno("Reset Settings", 
                                       "Reset all analysis settings to factory defaults?\n\n"
                                       "This will not affect loaded files or results.")
        if response:
            self.selected_species.set(DEFAULT_CONFIG['selected_species'])
            self.yaxis_auto.set(DEFAULT_CONFIG['yaxis_auto'])
            self.yaxis_min.set(DEFAULT_CONFIG['yaxis_min'])
            self.yaxis_max.set(DEFAULT_CONFIG['yaxis_max'])
            self.smoothing.set(DEFAULT_CONFIG['smoothing'])
            self.smoothing_ms.set(DEFAULT_CONFIG['smoothing_ms'])
            self.smooth_method.set(DEFAULT_CONFIG['smooth_method'])
            self.use_corrected_apd.set(DEFAULT_CONFIG['use_corrected_apd'])
            self.use_dual_path_detection.set(DEFAULT_CONFIG['use_dual_path_detection'])
            self.filter_outliers.set(DEFAULT_CONFIG['filter_outliers'])
            self.visual_filter_only.set(DEFAULT_CONFIG['visual_filter_only'])
            self.sync_zoom.set(DEFAULT_CONFIG['sync_zoom'])
            self.cardioid_immature_mode.set(DEFAULT_CONFIG['cardioid_immature_mode'])
            
            # Reset export settings
            for key, value in DEFAULT_CONFIG['export_settings'].items():
                if key in self.export_settings:
                    self.export_settings[key].set(value)
            
            self.on_yaxis_auto_toggle()
            
            # Re-plot current trace if available
            if self.all_results:
                self.plot_current_trace()
            
            messagebox.showinfo("Settings Reset", "All analysis settings have been reset to defaults.")
    
    def save_settings_and_exit(self):
        """Save settings before exit"""
        self.save_settings()
        if messagebox.askokcancel("Quit", "Do you want to quit APEX Platform?"):
            self.root.destroy()
    
    def reset_to_defaults(self):
        """Reset all settings to default values"""
        response = messagebox.askyesno("Reset Settings", 
                                       "Reset all settings to factory defaults?\n\n"
                                       "This will clear any saved preferences.")
        if response:
            for key, value in DEFAULT_CONFIG.items():
                if key == 'export_settings':
                    for subkey, subvalue in value.items():
                        if subkey in self.export_settings:
                            self.export_settings[subkey].set(subvalue)
                elif key == 'output_folder':
                    if value:
                        self.output_folder = Path.cwd() / "APEX_Professional_Output"
                        self.output_label.config(text=f"{self.output_folder}")
                elif key == 'smoothing_ms':
                    self.smoothing_ms.set(value)
                elif key == 'cardioid_immature_mode':
                    self.cardioid_immature_mode.set(value)
                else:
                    if hasattr(self, key):
                        getattr(self, key).set(value)
                    elif key == 'selected_species':
                        self.selected_species.set(value)
            
            self.on_yaxis_auto_toggle()
            messagebox.showinfo("Settings Reset", "All settings have been reset to defaults.")
    
    def get_smoothing_ms_value(self):
        """Safely get smoothing_ms value, handling empty string"""
        try:
            val = self.smoothing_ms.get()
            if val == '' or val is None:
                return None
            return float(val)
        except (tk.TclError, ValueError):
            return None
    
    def show_immature_mode_smoothing_suggestion(self):
        """Display suggestion for smoothing when cardioid immature mode is enabled"""
        current_smoothing = self.get_smoothing_ms_value()
        if current_smoothing is None or current_smoothing <= 3.0:
            messagebox.showinfo("Cardioid Immature Mode",
                               "Cardioid Immature Mode is enabled.\n\n"
                               "For early-stage cardioid cells, we recommend:\n"
                               "• Smoothing window: 5-10 ms\n"
                               "• APA thresholds: lowered to 10 mV\n"
                               "• APD90 thresholds: lowered to 25 ms\n"
                               "• dV/dt_max thresholds: lowered to 5 mV/ms\n\n"
                               "You can adjust smoothing in the Analysis Parameters panel.")
    
    def on_species_change(self, *args):
        species = self.selected_species.get()
        if species != 'auto':
            suggested = get_species_smoothing_suggestion(species)
            print(f"Info: For {species}, recommended smoothing: {suggested} ms")
            if hasattr(self, 'smoothing_ms'):
                current = self.get_smoothing_ms_value()
                if current is None or current <= 0:
                    print(f"  Setting adaptive smoothing to {suggested} ms")
        
        # CHANGE 2: Show suggestion when cardioid immature mode is enabled and species is cardioid
        if species == 'cardioid' and self.cardioid_immature_mode.get():
            self.show_immature_mode_smoothing_suggestion()
    
    def clear_correction_of_type(self, trace_idx, ap_idx, correction_type):
        trace = self.all_results[trace_idx]
        trace_id = trace.get('trace_id')
        
        if correction_type == 'peak':
            if trace_id in self.manual_peak_corrections:
                if ap_idx in self.manual_peak_corrections[trace_id]:
                    del self.manual_peak_corrections[trace_id][ap_idx]
            if ap_idx < len(trace['ap_metrics']):
                ap = trace['ap_metrics'][ap_idx]
                ap['has_manual_correction'] = False
                if 'peak' in ap.get('correction_type', ''):
                    if ap['correction_type'] == 'manual_peak':
                        ap['correction_type'] = 'auto'
                    elif '+peak' in ap['correction_type']:
                        ap['correction_type'] = ap['correction_type'].replace('+peak', '')
                    elif 'peak+' in ap['correction_type']:
                        ap['correction_type'] = ap['correction_type'].replace('peak+', '')
        
        elif correction_type == 'upstroke':
            if trace_id in self.manual_upstroke_corrections:
                if ap_idx in self.manual_upstroke_corrections[trace_id]:
                    del self.manual_upstroke_corrections[trace_id][ap_idx]
            if ap_idx < len(trace['ap_metrics']):
                ap = trace['ap_metrics'][ap_idx]
                ap['has_manual_upstroke'] = False
                if 'upstroke' in ap.get('correction_type', ''):
                    if ap['correction_type'] == 'manual_upstroke':
                        ap['correction_type'] = 'auto'
                    elif '+upstroke' in ap['correction_type']:
                        ap['correction_type'] = ap['correction_type'].replace('+upstroke', '')
                    elif 'upstroke+' in ap['correction_type']:
                        ap['correction_type'] = ap['correction_type'].replace('upstroke+', '')
        
        elif correction_type == 'late_repol':
            if trace_id in self.late_repolarization_corrections:
                if ap_idx in self.late_repolarization_corrections[trace_id]:
                    del self.late_repolarization_corrections[trace_id][ap_idx]
            if ap_idx < len(trace['ap_metrics']):
                ap = trace['ap_metrics'][ap_idx]
                ap['has_late_repol'] = False
                ap['late_repolarization_corrected'] = False
                if 'late_repol' in ap.get('correction_type', ''):
                    if ap['correction_type'] == 'late_repol':
                        ap['correction_type'] = 'auto'
                    elif '+late_repol' in ap['correction_type']:
                        ap['correction_type'] = ap['correction_type'].replace('+late_repol', '')
                    elif 'late_repol+' in ap['correction_type']:
                        ap['correction_type'] = ap['correction_type'].replace('late_repol+', '')
        
        if trace_id in self.manual_peak_corrections and not self.manual_peak_corrections[trace_id]:
            del self.manual_peak_corrections[trace_id]
        if trace_id in self.manual_upstroke_corrections and not self.manual_upstroke_corrections[trace_id]:
            del self.manual_upstroke_corrections[trace_id]
        if trace_id in self.late_repolarization_corrections and not self.late_repolarization_corrections[trace_id]:
            del self.late_repolarization_corrections[trace_id]
    
    def apply_correction_to_single_ap(self, trace_idx, ap_idx, correction_type, correction_value):
        if trace_idx >= len(self.all_results):
            return
    
        dat = self.all_results[trace_idx]
        trace_id = dat.get('trace_id')
    
        print(f"\n=== Applying {correction_type} correction to trace {trace_idx}, AP {ap_idx} ===")
        print(f"Before correction: {len(dat.get('ap_metrics', []))} APs in trace")
    
        self.clear_correction_of_type(trace_idx, ap_idx, correction_type)
    
        if correction_type == 'peak':
            if trace_id not in self.manual_peak_corrections:
                self.manual_peak_corrections[trace_id] = {}
            self.manual_peak_corrections[trace_id][ap_idx] = correction_value
        
            self.reanalyze_trace_with_correction(trace_idx, ap_idx, correction_value)
        
        elif correction_type == 'upstroke':
            if trace_id not in self.manual_upstroke_corrections:
                self.manual_upstroke_corrections[trace_id] = {}
            self.manual_upstroke_corrections[trace_id][ap_idx] = correction_value
        
            self.reanalyze_trace_with_upstroke_correction(trace_idx, ap_idx, correction_value)
    
        print(f"After correction: {len(self.all_results[trace_idx].get('ap_metrics', []))} APs in trace")
        for i, ap in enumerate(self.all_results[trace_idx].get('ap_metrics', [])):
            print(f"  AP {i}: peak at {ap.get('peak_time', 0):.1f}ms, type={ap.get('correction_type', 'auto')}")
    
    def reanalyze_trace_with_correction(self, trace_idx, ap_idx, corrected_peak_idx):
        if trace_idx >= len(self.all_results):
            return

        dat = self.all_results[trace_idx]
        time = dat['time']
        voltage = dat['voltage_raw']

        smoothing = self.smoothing.get()
        method = self.smooth_method.get()
        smoothing_ms = self.get_smoothing_ms_value()
        species = dat.get('species', 'default')
        use_corrected_apd = self.use_corrected_apd.get()

        dt_ms = float(time[1] - time[0]) if len(time) > 1 else 0.1
    
        if smoothing_ms is None or smoothing_ms <= 0:
            smoothing_ms = calculate_adaptive_smoothing(dt_ms, species, dat.get('file_type', 'CSV'))
    
        # Create the fully smoothed trace for visualization
        v_smooth = smooth_voltage(voltage, method=method, window_ms=smoothing_ms, dt_ms=dt_ms) if smoothing else voltage
    
        # CRITICAL FIX: Create minimally-smoothed trace for accurate upstroke detection
        minimal_smoothing_ms = 0
        v_minimal_smooth = smooth_voltage(voltage, method='savgol',
                                        window_ms=minimal_smoothing_ms, dt_ms=dt_ms) if dt_ms > 0 else voltage

        detection = {
            'stim_times_idx': dat['detection'].get('stim_times_idx', []),
            'stim_times_ms': dat['detection'].get('stim_times_ms', []),
            'real_ap_peaks_idx': np.array([corrected_peak_idx], dtype=int),
            'raw_peaks': dat['detection'].get('raw_peaks', []),
            'smooth_peaks': dat['detection'].get('smooth_peaks', [])
        }

        ap_metrics = []

        trace_id = dat.get('trace_id')
        upstroke_correction = None
        if trace_id and trace_id in self.manual_upstroke_corrections:
            if ap_idx in self.manual_upstroke_corrections[trace_id]:
                upstroke_correction = self.manual_upstroke_corrections[trace_id][ap_idx]

        # Get immature mode status
        immature_mode = self.cardioid_immature_mode.get() and species == 'cardioid'

        try:
            # CRITICAL FIX: Use v_minimal_smooth (NOT v_smooth) for upstroke detection
            m = compute_apd_metrics_enhanced_v3(time, v_minimal_smooth, corrected_peak_idx, 
                                                detection.get('stim_times_idx', []),
                                                species, use_corrected_apd, upstroke_correction,
                                                immature_mode=immature_mode)
        
            m['has_manual_correction'] = True
            if upstroke_correction is not None:
                m['correction_type'] = 'manual_peak+manual_upstroke'
                m['has_manual_upstroke'] = True
            else:
                m['correction_type'] = 'manual_peak'
        
            if trace_id and trace_id in self.late_repolarization_corrections:
                if ap_idx in self.late_repolarization_corrections[trace_id]:
                    rmp = m.get('RMP', np.nan)
                    peak_v = v_minimal_smooth[corrected_peak_idx] if corrected_peak_idx < len(v_minimal_smooth) else np.nan
                    apply_late_repolarization_correction_to_metrics(time, v_minimal_smooth, m, corrected_peak_idx, rmp, peak_v)
                    m['has_late_repol'] = True
                    current_type = m.get('correction_type', 'auto')
                    if 'late_repol' not in current_type:
                        m['correction_type'] = f'{current_type}+late_repol'
        
            if species == 'cardioid':
                is_valid, reason = is_cardioid_ap(m, species, immature_mode)
            else:
                is_valid, reason = is_physiologically_valid_ap(m, species, immature_mode=immature_mode)
            if is_valid:
                ap_metrics.append(m)
                print(f"  Added corrected AP: peak at {m['peak_time']:.1f}ms, dVdt={m['dVdt_max']:.1f}, type={m['correction_type']}")
            else:
                print(f"  Rejected AP after peak correction: {reason}")
        
        except Exception as e:
            print(f"Error computing metrics: {e}")

        apd90_values = [m.get('APD90', np.nan) for m in ap_metrics if not math.isnan(m.get('APD90', np.nan))]
        stv_apd90, stv_note = calculate_stv(apd90_values)

        result = {
            'time': np.array(time),
            'voltage_raw': np.array(voltage),
            'voltage_smooth': np.array(v_smooth),
            'voltage_minimal_smooth': np.array(v_minimal_smooth),
            'dt_ms': dt_ms,
            'detection': detection,
            'ap_metrics': ap_metrics,
            'stv_apd90': stv_apd90,
            'stv_note': stv_note,
            'dual_path_used': True,
            'use_corrected_apd': use_corrected_apd,
            'has_manual_correction': True,
            'adaptive_smoothing_used': self.get_smoothing_ms_value() is None or self.get_smoothing_ms_value() <= 0,
            'smoothing_ms_used': smoothing_ms,
            'sampling_rate_hz': 1000.0 / dt_ms if dt_ms > 0 else 1000,
            'immature_mode_used': immature_mode
        }

        result.update({
            'file': dat.get('file'),
            'file_name': dat.get('file_name'),
            'cell_id': dat.get('cell_id'),
            'display_cell_id': dat.get('display_cell_id'),
            'frequency': dat.get('frequency'),
            'file_type': dat.get('file_type'),
            'sweep_number': dat.get('sweep_number'),
            'total_sweeps': dat.get('total_sweeps'),
            'trace_id': dat.get('trace_id'),
            'species': species,
            'drug': dat.get('drug', 'None'),
            'concentration': dat.get('concentration', ''),
            'range_name': dat.get('range_name', '')
        })

        self.all_results[trace_idx] = result
        print(f"Trace {trace_idx} now has {len(ap_metrics)} AP(s)")

    def reanalyze_trace_with_upstroke_correction(self, trace_idx, ap_idx, start_idx):
        if trace_idx >= len(self.all_results):
            return

        dat = self.all_results[trace_idx]
        time = dat['time']
        voltage = dat['voltage_raw']

        smoothing = self.smoothing.get()
        method = self.smooth_method.get()
        smoothing_ms = self.get_smoothing_ms_value()
        species = dat.get('species', 'default')
        use_corrected_apd = self.use_corrected_apd.get()

        dt_ms = float(time[1] - time[0]) if len(time) > 1 else 0.1
    
        if smoothing_ms is None or smoothing_ms <= 0:
            smoothing_ms = calculate_adaptive_smoothing(dt_ms, species, dat.get('file_type', 'CSV'))
    
        # Create the fully smoothed trace for visualization
        v_smooth = smooth_voltage(voltage, method=method, window_ms=smoothing_ms, dt_ms=dt_ms) if smoothing else voltage
    
        # CRITICAL FIX: Create minimally-smoothed trace for accurate upstroke detection
        minimal_smoothing_ms = 0
        v_minimal_smooth = smooth_voltage(voltage, method='savgol',
                                        window_ms=minimal_smoothing_ms, dt_ms=dt_ms) if dt_ms > 0 else voltage

        detection = dat['detection'].copy()
        peaks = detection.get('real_ap_peaks_idx', [])

        if ap_idx >= len(peaks):
            print(f"Warning: AP index {ap_idx} out of range (only {len(peaks)} peaks)")
            return

         # Get immature mode status
        immature_mode = self.cardioid_immature_mode.get() and species == 'cardioid'

        ap_metrics = []

        for idx, peak_idx in enumerate(peaks):
            try:
                manual_upstroke = start_idx if idx == ap_idx else None
        
                trace_id = dat.get('trace_id')
                has_manual_peak = False
                if trace_id and trace_id in self.manual_peak_corrections:
                    if idx in self.manual_peak_corrections[trace_id]:
                        has_manual_peak = True
        
                # CRITICAL FIX: Use minimally-smoothed trace (v_minimal_smooth) for upstroke detection
                # This preserves the true upstroke velocity even with high global smoothing
                m = compute_apd_metrics_enhanced_v3(time, v_minimal_smooth, peak_idx, 
                                                    detection.get('stim_times_idx', []),
                                                    species, use_corrected_apd, manual_upstroke,
                                                    immature_mode=immature_mode)
        
                if has_manual_peak:
                    m['has_manual_correction'] = True
        
                if idx == ap_idx:
                    m['has_manual_upstroke'] = True
                    if has_manual_peak:
                        m['correction_type'] = 'manual_peak+manual_upstroke'
                    else:
                        m['correction_type'] = 'manual_upstroke'
                else:
                    if idx < len(dat['ap_metrics']):
                        old_ap = dat['ap_metrics'][idx]
                        m['correction_type'] = old_ap.get('correction_type', 'auto')
                        m['has_manual_correction'] = old_ap.get('has_manual_correction', False)
                        m['has_manual_upstroke'] = old_ap.get('has_manual_upstroke', False)
        
                if trace_id and trace_id in self.late_repolarization_corrections:
                    if idx in self.late_repolarization_corrections[trace_id]:
                        rmp = m.get('RMP', np.nan)
                        peak_v = v_minimal_smooth[peak_idx] if peak_idx < len(v_minimal_smooth) else np.nan
                        apply_late_repolarization_correction_to_metrics(time, v_minimal_smooth, m, peak_idx, rmp, peak_v)
                        m['has_late_repol'] = True
                        current_type = m.get('correction_type', 'auto')
                        if 'late_repol' not in current_type:
                            if current_type == 'auto':
                                m['correction_type'] = 'late_repol'
                            else:
                                m['correction_type'] = f'{current_type}+late_repol'
        
                if species == 'cardioid':
                    is_valid, reason = is_cardioid_ap(m, species, immature_mode)
                else:
                    is_valid, reason = is_physiologically_valid_ap(m, species, immature_mode=immature_mode)
                if is_valid:
                    ap_metrics.append(m)
                else:
                    print(f"Rejected AP after upstroke correction: {reason}")
            
            except Exception as e:
                print(f"Error computing metrics with upstroke correction: {e}")
                continue

        apd90_values = [m.get('APD90', np.nan) for m in ap_metrics if not math.isnan(m.get('APD90', np.nan))]
        stv_apd90, stv_note = calculate_stv(apd90_values)

        result = {
            'time': np.array(time),
            'voltage_raw': np.array(voltage),
            'voltage_smooth': np.array(v_smooth),
            'voltage_minimal_smooth': np.array(v_minimal_smooth),
            'dt_ms': dt_ms,
            'detection': detection,
            'ap_metrics': ap_metrics,
            'stv_apd90': stv_apd90,
            'stv_note': stv_note,
            'dual_path_used': True,
            'use_corrected_apd': use_corrected_apd,
            'has_upstroke_correction': True,
            'adaptive_smoothing_used': self.get_smoothing_ms_value() is None or self.get_smoothing_ms_value() <= 0,
            'smoothing_ms_used': smoothing_ms,
            'sampling_rate_hz': 1000.0 / dt_ms if dt_ms > 0 else 1000,
            'immature_mode_used': immature_mode
        }

        result.update({
            'file': dat.get('file'),
            'file_name': dat.get('file_name'),
            'cell_id': dat.get('cell_id'),
            'display_cell_id': dat.get('display_cell_id'),
            'frequency': dat.get('frequency'),
            'file_type': dat.get('file_type'),
            'sweep_number': dat.get('sweep_number'),
            'total_sweeps': dat.get('total_sweeps'),
            'trace_id': dat.get('trace_id'),
            'species': species,
            'drug': dat.get('drug', 'None'),
            'concentration': dat.get('concentration', ''),
            'range_name': dat.get('range_name', '')
        })

        self.all_results[trace_idx] = result
        print(f"  After upstroke correction: {len(ap_metrics)} APs in trace")
        for i, ap in enumerate(ap_metrics):
            print(f"    AP {i}: peak at {ap.get('peak_time', 0):.1f}ms, dVdt={ap.get('dVdt_max', 0):.1f}, upstroke_manual={ap.get('has_manual_upstroke', False)}")
    
    def build_enhanced_ui(self):
        """Build enhanced GUI with collapsible panels and styled buttons"""
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        left_frame = ttk.Frame(main_paned, width=400)
        
        left_canvas = tk.Canvas(left_frame)
        left_scrollbar = ttk.Scrollbar(left_frame, orient=tk.VERTICAL, command=left_canvas.yview)
        scrollable_frame = ttk.Frame(left_canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: left_canvas.configure(scrollregion=left_canvas.bbox("all"))
        )
        
        left_canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        left_canvas.configure(yscrollcommand=left_scrollbar.set)
        
        left_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        left_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        about_frame = ttk.Frame(scrollable_frame)
        about_frame.pack(fill=tk.X, pady=(0, 10))
        ttk.Button(about_frame, text="About APEX Platform",
                   command=self.show_about_dialog, width=20).pack(pady=5)
        
        self.file_panel = CollapsiblePanel(scrollable_frame, "File Management")
        self.file_panel.pack(fill=tk.X, pady=(0, 10))
        
        columns = ("File", "Cell ID", "Frequency", "Type", "Status", "Ranges", "Species")
        self.file_listbox = ttk.Treeview(self.file_panel.content_frame, columns=columns, show='headings', height=6)
        
        column_widths = {"File": 150, "Cell ID": 80, "Frequency": 60, "Type": 80, "Status": 60, "Ranges": 80, "Species": 80}
        for col in columns:
            self.file_listbox.heading(col, text=col)
            self.file_listbox.column(col, width=column_widths.get(col, 100))
        
        self.file_listbox.pack(fill=tk.BOTH, expand=True, pady=5)
        
        file_btn_frame = ttk.Frame(self.file_panel.content_frame)
        file_btn_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(file_btn_frame, text="Add Files", command=self.add_files_dialog, width=12).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_btn_frame, text="Add ABF Files", command=self.add_abf_files_dialog, width=12).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_btn_frame, text="Enhanced Stacking", command=self.show_enhanced_stacking, width=15).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_btn_frame, text="Edit Metadata", command=self.edit_all_metadata, width=12).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_btn_frame, text="Remove", command=self.remove_selected_file, width=10).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_btn_frame, text="Clear All", command=self.clear_all_files, width=10).pack(side=tk.LEFT, padx=2)
        
        output_frame = ttk.Frame(self.file_panel.content_frame)
        output_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(output_frame, text="Output Folder", command=self.choose_output_folder, width=12).pack(side=tk.LEFT, padx=2)
        self.output_label = tk.Label(output_frame, text=f"{self.output_folder}", anchor='w',
                                     font=("Helvetica", 8), foreground="blue")
        self.output_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        
        self.analysis_panel = CollapsiblePanel(scrollable_frame, "Analysis Parameters")
        self.analysis_panel.pack(fill=tk.X, pady=(0, 10))
        
        smoothing_frame = ttk.LabelFrame(self.analysis_panel.content_frame, text="Smoothing", padding=5)
        smoothing_frame.pack(fill=tk.X, pady=5)
        
        ttk.Checkbutton(smoothing_frame, text="Enable smoothing", variable=self.smoothing).pack(anchor='w', pady=2)
        
        method_frame = ttk.Frame(smoothing_frame)
        method_frame.pack(fill=tk.X, pady=2)
        ttk.Radiobutton(method_frame, text="Savitzky-Golay", variable=self.smooth_method, value='savgol').pack(anchor='w')
        ttk.Radiobutton(method_frame, text="Gaussian", variable=self.smooth_method, value='gaussian').pack(anchor='w')
        
        ttk.Label(smoothing_frame, text="Smoothing window (ms):").pack(anchor='w', pady=(5, 0))
        ttk.Label(smoothing_frame, text="(leave empty for adaptive, 0 = no smoothing)", font=("Helvetica", 8, "italic"), foreground="gray").pack(anchor='w')
        self.smoothing_ms_entry = ttk.Entry(smoothing_frame, textvariable=self.smoothing_ms, width=15)
        self.smoothing_ms_entry.pack(anchor='w', pady=2)
        
        peak_frame = ttk.LabelFrame(self.analysis_panel.content_frame, text="Peak Detection", padding=5)
        peak_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(peak_frame, text="Min APD90 (ms):").pack(anchor='w')
        ttk.Entry(peak_frame, textvariable=self.min_apd90, width=15).pack(anchor='w', pady=2)
        
        ttk.Checkbutton(peak_frame, text="Use dual-path detection",
                        variable=self.use_dual_path_detection).pack(anchor='w', pady=2)
        
        ttk.Checkbutton(peak_frame, text="Skip stimulation artifacts",
                        variable=self.use_biological_detection).pack(anchor='w', pady=2)
        
        species_frame = ttk.LabelFrame(self.analysis_panel.content_frame, text="Species", padding=5)
        species_frame.pack(fill=tk.X, pady=5)
        
        ttk.Radiobutton(species_frame, text="Auto-detect", variable=self.selected_species, value="auto").pack(anchor='w', pady=2)
        ttk.Radiobutton(species_frame, text="Rabbit", variable=self.selected_species, value="rabbit").pack(anchor='w', pady=2)
        ttk.Radiobutton(species_frame, text="Mouse", variable=self.selected_species, value="mouse").pack(anchor='w', pady=2)
        ttk.Radiobutton(species_frame, text="Zebrafish", variable=self.selected_species, value="zebrafish").pack(anchor='w', pady=2)
        ttk.Radiobutton(species_frame, text="Cardioid", variable=self.selected_species, value="cardioid").pack(anchor='w', pady=2)
        
        # CHANGE 2: Add Cardioid Immature Mode checkbox
        self.immature_mode_cb = ttk.Checkbutton(species_frame, 
                                               text="Cardioid Immature Mode (lower thresholds for early-stage cells)",
                                               variable=self.cardioid_immature_mode)
        self.immature_mode_cb.pack(anchor='w', pady=2)
        
        self.visualization_panel = CollapsiblePanel(scrollable_frame, "Visualization")
        self.visualization_panel.pack(fill=tk.X, pady=(0, 10))
        
        yaxis_frame = ttk.LabelFrame(self.visualization_panel.content_frame, text="Y-axis Settings", padding=5)
        yaxis_frame.pack(fill=tk.X, pady=5)
        
        ttk.Checkbutton(yaxis_frame, text="Auto detect range", variable=self.yaxis_auto,
                        command=self.on_yaxis_auto_toggle).pack(anchor='w', pady=2)
        
        manual_frame = ttk.Frame(yaxis_frame)
        manual_frame.pack(fill=tk.X, pady=2)
        
        ttk.Label(manual_frame, text="Min:").pack(side=tk.LEFT, padx=(0, 2))
        self.yaxis_min_entry = ttk.Entry(manual_frame, textvariable=self.yaxis_min, width=8, state='disabled')
        self.yaxis_min_entry.pack(side=tk.LEFT, padx=2)
        
        ttk.Label(manual_frame, text="Max:").pack(side=tk.LEFT, padx=(10, 2))
        self.yaxis_max_entry = ttk.Entry(manual_frame, textvariable=self.yaxis_max, width=8, state='disabled')
        self.yaxis_max_entry.pack(side=tk.LEFT, padx=2)
        
        ttk.Button(manual_frame, text="Apply", command=self.apply_yaxis_range, width=8).pack(side=tk.LEFT, padx=10)
        ttk.Button(manual_frame, text="Auto Detect", command=self.auto_detect_yaxis_range, width=10).pack(side=tk.LEFT, padx=5)
        
        ttk.Checkbutton(yaxis_frame, text="Visual filtering only (preserves AP shape)",
                        variable=self.visual_filter_only).pack(anchor='w', pady=2)
        ttk.Checkbutton(yaxis_frame, text="Filter outliers", variable=self.filter_outliers).pack(anchor='w', pady=2)
        ttk.Checkbutton(yaxis_frame, text="Sync zoom across traces", variable=self.sync_zoom).pack(anchor='w', pady=2)
        
        self.export_panel = CollapsiblePanel(scrollable_frame, "Results Export")
        self.export_panel.pack(fill=tk.X, pady=(0, 10))
        
        export_options_frame = ttk.LabelFrame(self.export_panel.content_frame, text="Export Options", padding=5)
        export_options_frame.pack(fill=tk.X, pady=5)
        
        export_notebook = ttk.Notebook(export_options_frame)
        export_notebook.pack(fill=tk.BOTH, expand=True, pady=5)
        
        data_tab = ttk.Frame(export_notebook)
        export_notebook.add(data_tab, text="Data Export")
        
        ttk.Checkbutton(data_tab, text="AP Parameter Matrix (5 sheets)",
                        variable=self.export_settings['ap_parameter_matrix']).pack(anchor='w', pady=2)
        ttk.Checkbutton(data_tab, text="RAW AP Data Table",
                        variable=self.export_settings['raw_ap_data']).pack(anchor='w', pady=2)
        ttk.Checkbutton(data_tab, text="Frequency/Drug Response",
                        variable=self.export_settings['frequency_drug_response']).pack(anchor='w', pady=2)
        ttk.Checkbutton(data_tab, text="Comprehensive Analysis",
                        variable=self.export_settings['comprehensive_analysis']).pack(anchor='w', pady=2)
        
        traces_tab = ttk.Frame(export_notebook)
        export_notebook.add(traces_tab, text="Traces Export")
        
        ttk.Checkbutton(traces_tab, text="Individual Traces (CSV)",
                        variable=self.export_settings['individual_traces']).pack(anchor='w', pady=2)
        ttk.Checkbutton(traces_tab, text="Average Traces (CSV)",
                        variable=self.export_settings['average_traces']).pack(anchor='w', pady=2)
        
        figure_tab = ttk.Frame(export_notebook)
        export_notebook.add(figure_tab, text="Figure Export")
        
        fig_canvas = tk.Canvas(figure_tab)
        fig_scrollbar = ttk.Scrollbar(figure_tab, orient=tk.VERTICAL, command=fig_canvas.yview)
        fig_scrollable_frame = ttk.Frame(fig_canvas)
        
        fig_scrollable_frame.bind(
            "<Configure>",
            lambda e: fig_canvas.configure(scrollregion=fig_canvas.bbox("all"))
        )
        
        fig_canvas.create_window((0, 0), window=fig_scrollable_frame, anchor="nw")
        fig_canvas.configure(yscrollcommand=fig_scrollbar.set)
        
        fig_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        fig_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        ttk.Label(fig_scrollable_frame, text="Requested Figures:", font=("Helvetica", 10, "bold")).pack(anchor='w', pady=(5, 2), padx=5)
        
        ttk.Checkbutton(fig_scrollable_frame, text="1. AP Overlay (RAW) - Beat-to-Beat Variability",
                        variable=self.export_settings['ap_overlay_raw']).pack(anchor='w', pady=2, padx=5)
        ttk.Checkbutton(fig_scrollable_frame, text="2. Average AP ± SEM - Morphology Summary",
                        variable=self.export_settings['average_ap_sem']).pack(anchor='w', pady=2, padx=5)
        
        special_frame = tk.Frame(fig_scrollable_frame)
        special_frame.pack(anchor='w', pady=(5, 0), padx=15, fill=tk.X)
        
        checkbox_canvas = tk.Canvas(special_frame, width=16, height=16, highlightthickness=0, bd=0)
        checkbox_canvas.pack(side=tk.LEFT, padx=(0, 10))
        checkbox_canvas.create_rectangle(2, 2, 14, 14, outline='gray', width=1)
        
        self.special_check_var = tk.BooleanVar(value=False)
        
        def toggle_special_check():
            current = self.special_check_var.get()
            self.special_check_var.set(not current)
            self.export_settings['one_figure_per_cell'].set(not current)
            update_checkbox_display()
        
        def update_checkbox_display():
            checkbox_canvas.delete("check")
            if self.special_check_var.get():
                checkbox_canvas.create_line(4, 8, 7, 11, 12, 4, fill='black', width=2, tag="check")
        
        checkbox_canvas.bind('<Button-1>', lambda e: toggle_special_check())
        tk.Label(special_frame,
                 text="↳ Create 1 figure for AP Overlay & Average AP (if >1 condition per cell)",
                 font=("Helvetica", 9, "italic"),
                 fg="#07134F",
                 anchor='w').pack(side=tk.LEFT)
        
        ttk.Checkbutton(fig_scrollable_frame, text="3. Drug Comparison Multi-Panel",
                        variable=self.export_settings['drug_comparison']).pack(anchor='w', pady=2, padx=5)
        ttk.Checkbutton(fig_scrollable_frame, text="4. Frequency Comparison Multi-Panel",
                        variable=self.export_settings['frequency_comparison']).pack(anchor='w', pady=2, padx=5)
        ttk.Checkbutton(fig_scrollable_frame, text="5. Poincaré Plot for STV Visualization",
                        variable=self.export_settings['stv_analysis']).pack(anchor='w', pady=2, padx=5)
        ttk.Checkbutton(fig_scrollable_frame, text="6. Normalized AP Overlay",
                        variable=self.export_settings['normalized_ap']).pack(anchor='w', pady=2, padx=5)
        
        ttk.Button(fig_scrollable_frame, text="Select All Figures",
                   command=self.select_all_figures, width=20).pack(pady=10, padx=5)
        
        name_frame = ttk.Frame(export_options_frame)
        name_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(name_frame, text="Export Name:").pack(side=tk.LEFT, padx=5)
        self.export_name_var = tk.StringVar(value=f"APEX_Export_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}")
        ttk.Entry(name_frame, textvariable=self.export_name_var, width=30).pack(side=tk.LEFT, padx=5)
        
        export_btn_frame = ttk.Frame(self.export_panel.content_frame)
        export_btn_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(export_btn_frame, text="Export Selected Results",
                   command=self.export_selected_results, width=20).pack(side=tk.LEFT, padx=5)
        ttk.Button(export_btn_frame, text="Export All Results",
                   command=self.export_all_results, width=20).pack(side=tk.LEFT, padx=5)
        ttk.Button(export_btn_frame, text="Export Stacked Files",
                   command=self.export_stacked_files_only, width=20).pack(side=tk.LEFT, padx=5)
        
        # Validation & Actions panel - Now with Configuration buttons
        action_frame = ttk.LabelFrame(scrollable_frame, text="Validation & Actions", padding=10)
        action_frame.pack(fill=tk.X, pady=(0, 10))
        
        run_btn_frame = ttk.Frame(action_frame)
        run_btn_frame.pack(fill=tk.X, pady=5)
        
        self.run_btn = tk.Button(run_btn_frame, text="▶ RUN ENHANCED ANALYSIS",
                                 command=self.run_professional_analysis,
                                 bg="#4CAF50", fg="white", font=("Helvetica", 10, "bold"),
                                 height=2, relief=tk.RAISED, bd=3)
        self.run_btn.pack(fill=tk.X, pady=2)
        
        # Reanalyze All button
        reanalyze_frame = ttk.Frame(action_frame)
        reanalyze_frame.pack(fill=tk.X, pady=2)
        self.reanalyze_btn = tk.Button(reanalyze_frame, text="⟳ REANALYZE ALL",
                                       command=self.reanalyze_all_traces,
                                       bg="#F39C12", fg="white", font=("Helvetica", 10, "bold"),
                                       height=1, relief=tk.RAISED, bd=2)
        self.reanalyze_btn.pack(fill=tk.X)
        
        # Configuration buttons (Save/Load/Reset)
        config_btn_frame = ttk.Frame(action_frame)
        config_btn_frame.pack(fill=tk.X, pady=2)
        
        self.save_config_btn = tk.Button(config_btn_frame, text="💾 Save Configuration",
                                         command=self.save_configuration_to_file,
                                         bg="#2E86C1", fg="white", font=("Helvetica", 9, "bold"),
                                         height=1, relief=tk.RAISED, bd=2)
        self.save_config_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        
        self.load_config_btn = tk.Button(config_btn_frame, text="📂 Load Configuration",
                                         command=self.load_configuration_from_file,
                                         bg="#F39C12", fg="white", font=("Helvetica", 9, "bold"),
                                         height=1, relief=tk.RAISED, bd=2)
        self.load_config_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 2))
        
        self.reset_config_btn = tk.Button(config_btn_frame, text="⟲ Reset Analysis Settings",
                                          command=self.reset_analysis_settings,
                                          bg="#E74C3C", fg="white", font=("Helvetica", 9, "bold"),
                                          height=1, relief=tk.RAISED, bd=2)
        self.reset_config_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 0))
        
        self.progress = ttk.Progressbar(action_frame, orient=tk.HORIZONTAL, mode='determinate')
        self.progress.pack(fill=tk.X, pady=5)
        
        ttk.Button(action_frame, text="Validate All Traces", command=self.validate_all_traces).pack(fill=tk.X, pady=2)
        # Confirm Analysis button REMOVED
        
        main_paned.add(left_frame, weight=1)
        
        right_frame = ttk.Frame(main_paned)
        main_paned.add(right_frame, weight=2)
        
        plot_frame = ttk.LabelFrame(right_frame, text="Visualization", padding=5)
        plot_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))
        
        self.fig, self.ax = plt.subplots(figsize=(10, 6))
        self.fig.tight_layout()
        self.canvas = FigureCanvasTkAgg(self.fig, master=plot_frame)
        self.canvas_widget = self.canvas.get_tk_widget()
        self.canvas_widget.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        toolbar = NavigationToolbar2Tk(self.canvas, plot_frame)
        toolbar.update()
        self.canvas._tkcanvas.pack(fill=tk.BOTH, expand=False)
        
        self.canvas.mpl_connect('draw_event', self.on_draw_event)
        
        plot_controls = ttk.Frame(plot_frame)
        plot_controls.pack(fill=tk.X, pady=5)
        
        btn_peak = tk.Button(plot_controls, 
                            text="Interactive\nPeak Selector",
                            font=("Helvetica", 9, "bold"),
                            bg="#F39C12", fg="white",
                            width=18, height=2,
                            relief=tk.RAISED, bd=2,
                            command=self.start_enhanced_interactive_selection)
        btn_peak.pack(side=tk.LEFT, padx=5, expand=True, fill=tk.X)
        
        btn_upstroke = tk.Button(plot_controls,
                                text="Interactive\nUpstroke Start",
                                font=("Helvetica", 9, "bold"),
                                bg="#3498DB", fg="white",
                                width=18, height=2,
                                relief=tk.RAISED, bd=2,
                                command=self.start_upstroke_selection)
        btn_upstroke.pack(side=tk.LEFT, padx=5, expand=True, fill=tk.X)
        
        btn_repolarization = tk.Button(plot_controls,
                                      text="Late Repolarization\nCorrection",
                                      font=("Helvetica", 9, "bold"),
                                      bg="#9B59B6", fg="white",
                                      width=18, height=2,
                                      relief=tk.RAISED, bd=2,
                                      command=self.correct_current_trace_for_late_repolarization)
        btn_repolarization.pack(side=tk.LEFT, padx=5, expand=True, fill=tk.X)
        
        nav_frame = ttk.Frame(plot_frame)
        nav_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(nav_frame, text="⟵ Previous", command=self.prev_trace, width=12).pack(side=tk.LEFT, padx=5)
        ttk.Button(nav_frame, text="Next ⟶", command=self.next_trace, width=12).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(nav_frame, text="Validate Current",
                   command=self.validate_current_trace, width=15).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(nav_frame, text="Flag Problematic",
                   command=self.flag_current_trace, width=15).pack(side=tk.LEFT, padx=5)
        
        reject_frame = ttk.Frame(plot_frame)
        reject_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(reject_frame, text="Reject:").pack(side=tk.LEFT, padx=5)
        
        self.rejection_reason_var = tk.StringVar(value="Poor signal quality")
        reasons = ["Poor signal quality", "Unstable baseline", "No clear AP", "Artifact contamination", "Other"]
        reason_combo = ttk.Combobox(reject_frame, textvariable=self.rejection_reason_var,
                                    values=reasons, state="readonly", width=20)
        reason_combo.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(reject_frame, text="REJECT TRACE", command=self.reject_current_trace,
                   style="Red.TButton", width=15).pack(side=tk.LEFT, padx=5)
        
        results_frame = ttk.LabelFrame(right_frame, text="Results", padding=5)
        results_frame.pack(fill=tk.BOTH, expand=True)
        
        self.results_notebook = ttk.Notebook(results_frame)
        self.results_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        params_tab = ttk.Frame(self.results_notebook)
        self.results_notebook.add(params_tab, text="AP Parameters")
        
        cols = ("Validate", "File", "Cell", "Freq", "Drug", "Range", "Species", "Corr", "APA", "APD30", "APD50", "APD90", "dVdt_max", "RMP", "STV", "RepolFrac")
        self.tree = ttk.Treeview(params_tab, columns=cols, show='headings', height=8)
        
        column_names = {
            "Validate": "✓",
            "File": "File",
            "Cell": "Cell",
            "Freq": "Freq",
            "Drug": "Drug",
            "Range": "Range",
            "Species": "Species",
            "Corr": "Corr",
            "APA": "APA",
            "APD30": "APD30",
            "APD50": "APD50",
            "APD90": "APD90",
            "dVdt_max": "dV/dt max",
            "RMP": "RMP",
            "STV": "STV",
            "RepolFrac": "Repol Frac"
        }
        
        for c in cols:
            self.tree.heading(c, text=column_names[c])
            self.tree.column(c, width=50)
        
        tree_scroll = ttk.Scrollbar(params_tab, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=tree_scroll.set)
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.tree.bind('<ButtonRelease-1>', self.on_tree_select)
        
        stats_tab = ttk.Frame(self.results_notebook)
        self.results_notebook.add(stats_tab, text="Statistics")
        
        self.stats_text = scrolledtext.ScrolledText(stats_tab, height=10, font=("Courier", 9))
        self.stats_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.style = ttk.Style()
        self.style.configure("Red.TButton", foreground="red")
        self.style.configure("Accent.TButton", background="#4CAF50", foreground="white")
        
        self.root.bind('<Left>', lambda e: self.prev_trace())
        self.root.bind('<Right>', lambda e: self.next_trace())
        self.root.bind('<Control-v>', lambda e: self.validate_all_traces())
    
    def show_about_dialog(self):
        AboutAPEXDialog(self.root)
    
    def select_all_figures(self):
        figure_keys = ['ap_overlay_raw', 'average_ap_sem', 'drug_comparison',
                       'frequency_comparison', 'stv_analysis', 'normalized_ap']
        for key in figure_keys:
            self.export_settings[key].set(True)
    
    def edit_all_metadata(self):
        if not self.file_metadata:
            messagebox.showinfo("No Files", "Please load files first to edit metadata.")
            return
        
        editor = UniversalMetadataEditor(self.root, self.file_metadata, self.all_results)
        editor.wait_window()
        
        modified_metadata = editor.get_modified_metadata()
        
        if modified_metadata:
            for file_path, changes in modified_metadata.items():
                self.file_metadata[file_path] = changes['modified']
            
            self.update_file_list_display()
            
            if self.all_results:
                self.update_results_metadata(modified_metadata)
    
    def update_results_metadata(self, modified_metadata):
        for res in self.all_results:
            file_path = res.get('file')
            if file_path in modified_metadata:
                new_meta = modified_metadata[file_path]['modified']
                
                res['cell_id'] = new_meta.get('cell_id', res.get('cell_id'))
                res['display_cell_id'] = new_meta.get('display_cell_id', res.get('display_cell_id'))
                res['frequency'] = new_meta.get('frequency', res.get('frequency'))
                res['drug'] = new_meta.get('drug', res.get('drug'))
                res['concentration'] = new_meta.get('concentration', res.get('concentration'))
                res['species'] = new_meta.get('species', res.get('species'))
        
        self.update_results_table()
    
    def update_file_list_display(self):
        for item in self.file_listbox.get_children():
            self.file_listbox.delete(item)
        
        for file_path in self.file_list:
            meta = self.file_metadata.get(file_path, {})
            filename = Path(file_path).name
            file_type = "ABF" if file_path.endswith('.abf') else "CSV/Excel"
            cell_id = meta.get('cell_id', 'Unknown')
            frequency = meta.get('frequency', 'Unknown')
            species = meta.get('species', 'default')
            
            range_info = ""
            if file_path in self.abf_trace_selections:
                range_info = f"{len(self.abf_trace_selections[file_path])} ranges"
            
            self.file_listbox.insert('', tk.END, values=(
                filename,
                cell_id,
                frequency,
                file_type,
                "Loaded",
                range_info,
                species
            ))
        
        for group_name, stacked_data in self.stacked_files.items():
            cell_id = stacked_data.get('cell_id', group_name)
            frequency = stacked_data.get('frequency', 'Multiple')
            n_traces = stacked_data.get('n_traces', 0)
            
            self.file_listbox.insert('', tk.END, values=(
                f"Stacked_{group_name}",
                cell_id,
                frequency,
                f"Stacked ({n_traces} traces)",
                "Loaded",
                stacked_data.get('condition', ''),
                "auto"
            ))
    
    def start_enhanced_interactive_selection(self):
        if not self.all_results:
            messagebox.showwarning("No Trace", "No trace loaded for interactive selection.")
            return
        
        if self.interactive_selector:
            try:
                self.interactive_selector.clear()
            except Exception:
                pass
            self.interactive_selector = None
        
        dat = self.all_results[self.current_trace_index]
        self.interactive_selector = EnhancedInteractivePeakSelector(
            self.ax, self.canvas, dat, self.all_results, self.current_trace_index,
            self.on_peak_selected
        )
        
        self.plot_current_trace()
        
        messagebox.showinfo("Interactive Peak Selection",
                            "Interactive mode ACTIVE\n\n"
                            "1. Click directly on the trace to select AP peak\n"
                            "2. Drag the marker to adjust\n"
                            "3. Press Enter to confirm, Escape to cancel\n\n"
                            "APs with >95% similarity will be automatically selected for batch correction")
    
    def on_peak_selected(self, peak_idx, peak_time, peak_voltage, batch_apply=False):
        if not self.all_results:
            return

        self.apply_correction_to_single_ap(
            self.current_trace_index, 
            0,
            'peak', 
            peak_idx
        )

        updated_dat = self.all_results[self.current_trace_index]
    
        self.plot_current_trace()
        self.update_results_table()

        if batch_apply:
            if updated_dat.get('ap_metrics'):
                current_ap = updated_dat['ap_metrics'][0]
                dt_ms = updated_dat.get('dt_ms', 0.1)
                similar_aps = find_similar_aps_by_morphology(
                    current_ap, self.all_results, self.current_trace_index, 
                    0, threshold=0.70, dt_ms=dt_ms
                )
        
                if similar_aps:
                    current_trace_info = {
                        'file_name': updated_dat.get('file_name', 'unknown'),
                        'cell_id': updated_dat.get('cell_id', 'unknown'),
                        'frequency': updated_dat.get('frequency', 'unknown')
                    }
            
                    dialog = SelectiveBatchCorrectionDialog(
                        self.root, 'peak', current_ap, similar_aps, 
                        current_trace_info, self.get_ap_display_info
                    )
                    dialog.wait_window()
            
                    selected_pairs = dialog.get_selected_pairs()
                    if selected_pairs:
                        self.apply_batch_correction(selected_pairs, 'peak', peak_idx)
                        messagebox.showinfo("Batch Correction Complete", 
                                        f"Successfully corrected {len(selected_pairs)} APs")
    
    def start_upstroke_selection(self):
        if not self.all_results:
            messagebox.showwarning("No Trace", "No trace loaded for upstroke selection.")
            return
        
        if self.upstroke_selector:
            try:
                self.upstroke_selector.clear()
            except Exception:
                pass
            self.upstroke_selector = None
        
        dat = self.all_results[self.current_trace_index]
        
        if not dat.get('ap_metrics'):
            messagebox.showwarning("No AP Detected", "No AP detected in this trace. Please run analysis first.")
            return
        
        self.upstroke_selector = UpstrokeStartSelector(
            self.ax, self.canvas, dat, self.all_results, self.current_trace_index,
            self.on_upstroke_selected
        )
        
        self.plot_current_trace()
        
        messagebox.showinfo("Upstroke Start Selection",
                            "Move the mouse over the plot — a vertical cursor\n"
                            "will follow and snap onto the trace.\n\n"
                            "• Left-click to lock the cursor at that point\n"
                            "• ← / → keys nudge by one sample\n"
                            "• Enter accepts, Escape cancels\n"
                            "• Second click unlocks for fine-tuning")
    
    def on_upstroke_selected(self, start_idx, start_time, start_voltage, dvdt_max, batch_apply=False):
        if not self.all_results:
            return
    
        dat = self.all_results[self.current_trace_index]
        trace_id = dat.get('trace_id')
        current_ap_idx = 0
    
        self.apply_correction_to_single_ap(
            self.current_trace_index, 
            current_ap_idx, 
            'upstroke', 
            start_idx
        )
    
        self.plot_current_trace()
        self.update_results_table()
    
        if batch_apply:
            current_ap = dat['ap_metrics'][current_ap_idx] if dat.get('ap_metrics') else None
            if current_ap:
                dt_ms = dat.get('dt_ms', 0.1)
                similar_aps = find_similar_aps_by_morphology(
                    current_ap, self.all_results, self.current_trace_index, 
                    current_ap_idx, threshold=0.70, dt_ms=dt_ms
                )
            
                if similar_aps:
                    current_trace_info = {
                        'file_name': dat.get('file_name', 'unknown'),
                        'cell_id': dat.get('cell_id', 'unknown'),
                        'frequency': dat.get('frequency', 'unknown')
                    }
                
                    dialog = SelectiveBatchCorrectionDialog(
                        self.root, 'upstroke', current_ap, similar_aps, 
                        current_trace_info, self.get_ap_display_info
                    )
                    dialog.wait_window()
                
                    selected_pairs = dialog.get_selected_pairs()
                    if selected_pairs:
                        self.apply_batch_correction(selected_pairs, 'upstroke', start_idx)
                        messagebox.showinfo("Batch Correction Complete", 
                                        f"Successfully corrected {len(selected_pairs)} APs")
    
    def get_ap_display_info(self, trace_idx, ap_idx):
        if trace_idx >= len(self.all_results):
            return None
        
        trace = self.all_results[trace_idx]
        if ap_idx >= len(trace.get('ap_metrics', [])):
            return None
        
        ap = trace['ap_metrics'][ap_idx]
        
        file_name = trace.get('file_name', 'unknown')
        cell_id = trace.get('cell_id', 'unknown')
        frequency = trace.get('frequency', 'unknown')
        drug = trace.get('drug', 'None')
        
        trace_name = f"{file_name[:20]}_{cell_id}_{frequency}Hz"
        
        return {
            'trace_name': trace_name,
            'cell_id': cell_id,
            'frequency': frequency,
            'drug': drug,
            'apd90': ap.get('APD90', 0),
            'apa': ap.get('APA', 0),
            'dvdt': ap.get('dVdt_max', 0),
            'rmp': ap.get('RMP', 0)
        }
    
    def apply_batch_correction(self, selected_pairs, correction_type, correction_value):
        total = len(selected_pairs)
        
        progress_dialog = BatchProgressDialog(self.root, 
                                              f"Applying {correction_type.title()} Corrections", 
                                              total)
        
        for i, (trace_idx, ap_idx) in enumerate(selected_pairs):
            if progress_dialog.is_cancelled():
                break
            
            status_text = f"Correcting {i+1} of {total}: {correction_type} correction"
            progress_dialog.update(i + 1, status_text)
            
            self.apply_correction_to_single_ap(trace_idx, ap_idx, correction_type, correction_value)
        
        progress_dialog.close()
        
        self.update_results_table()
        if any(trace_idx == self.current_trace_index for trace_idx, _ in selected_pairs):
            self.plot_current_trace()
        
        messagebox.showinfo("Batch Correction Complete", 
                           f"Successfully corrected {len(selected_pairs)} APs")
    
    def correct_current_trace_for_late_repolarization(self):
        if not self.all_results:
            messagebox.showwarning("No Trace", "No trace loaded.")
            return
        
        dat = self.all_results[self.current_trace_index]
        
        if not dat.get('ap_metrics'):
            messagebox.showwarning("No AP Detected", "No AP detected in this trace.")
            return
        
        current_ap = dat['ap_metrics'][0]
        current_ap_idx = 0
        
        if current_ap.get('late_repolarization_corrected', False):
            result = messagebox.askyesno("Already Corrected",
                                         "This AP already has late repolarization correction applied.\n"
                                         "Do you want to reapply correction?")
            if not result:
                return
        
        rmp = current_ap.get('RMP', np.nan)
        peak_idx = current_ap.get('peak_idx', 0)
        if peak_idx < len(dat['voltage_smooth']):
            peak_v = dat['voltage_smooth'][peak_idx]
        else:
            peak_v = np.nan
        
        raw_apd80 = current_ap.get('APD80', np.nan)
        raw_apd90 = current_ap.get('APD90', np.nan)
        
        corrected_apd80, corrected_apd90, slope, intercept, fit_range = compute_corrected_apd_from_fit_v2(
            dat['time'], dat['voltage_smooth'], peak_idx, rmp, peak_v
        )
        
        if corrected_apd80 is None or corrected_apd90 is None:
            messagebox.showwarning("Correction Failed",
                                   "Could not compute corrected APD values.\n"
                                   "Check that repolarization phase has sufficient data points.")
            return
        
        dt_ms = dat.get('dt_ms', 0.1)
        similar_aps = find_similar_aps_by_morphology(
            current_ap, self.all_results, self.current_trace_index, current_ap_idx,
            threshold=0.70, dt_ms=dt_ms
        )
        
        dialog = tk.Toplevel(self.root)
        dialog.title("Late Repolarization Correction Preview")
        dialog.geometry("750x650")
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg='white')
        
        ttk.Label(dialog, text="Late Repolarization Correction",
                  font=("Helvetica", 12, "bold")).pack(pady=10)
        
        preview_fig, preview_ax = plt.subplots(figsize=(8, 4))
        
        time = dat['time']
        voltage = dat['voltage_smooth']
        
        t_start, t_end = fit_range
        
        preview_ax.plot(time, voltage, 'b-', linewidth=1.5, label='AP trace')
        
        t_fit = np.linspace(t_start, t_end, 100)
        v_fit = slope * t_fit + intercept
        preview_ax.plot(t_fit, v_fit, 'orange', linewidth=2, linestyle='--', 
                       label='Linear fit (APD50-APD70)')
        
        apa = peak_v - rmp if not math.isnan(peak_v) and not math.isnan(rmp) else 100
        v80 = rmp + 0.2 * apa
        v90 = rmp + 0.1 * apa
        
        t80 = (v80 - intercept) / slope
        t90 = (v90 - intercept) / slope
        
        if t80 > time[peak_idx]:
            preview_ax.plot(t80, v80, 'go', markersize=8, label='Corrected APD80')
            preview_ax.axvline(x=t80, color='green', linestyle=':', alpha=0.7)
        if t90 > time[peak_idx]:
            preview_ax.plot(t90, v90, 'g*', markersize=10, label='Corrected APD90')
            preview_ax.axvline(x=t90, color='green', linestyle=':', alpha=0.7)
        
        raw_apd80_time = time[peak_idx] + raw_apd80
        raw_apd90_time = time[peak_idx] + raw_apd90
        if raw_apd80_time < time[-1]:
            preview_ax.plot(raw_apd80_time, v80, 'ro', markersize=6, label='Raw APD80')
        if raw_apd90_time < time[-1]:
            preview_ax.plot(raw_apd90_time, v90, 'r*', markersize=8, label='Raw APD90')
        
        preview_ax.set_xlabel('Time (ms)')
        preview_ax.set_ylabel('Voltage (mV)')
        preview_ax.set_title('Late Repolarization Correction Preview (APD50-APD70 Fit)')
        preview_ax.legend(fontsize=8, loc='upper right')
        preview_ax.grid(True, alpha=0.3)
        
        preview_canvas = FigureCanvasTkAgg(preview_fig, master=dialog)
        preview_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        info_text = (
            f"Current values:\n"
            f"• Raw APD80: {raw_apd80:.1f} ms\n"
            f"• Raw APD90: {raw_apd90:.1f} ms\n\n"
            f"Corrected values:\n"
            f"• Corrected APD80: {corrected_apd80:.1f} ms\n"
            f"• Corrected APD90: {corrected_apd90:.1f} ms\n\n"
            f"Change:\n"
            f"• APD80: {corrected_apd80 - raw_apd80:+.1f} ms\n"
            f"• APD90: {corrected_apd90 - raw_apd90:+.1f} ms"
        )
        
        info_label = ttk.Label(dialog, text=info_text, justify=tk.LEFT, background='white')
        info_label.pack(pady=10, padx=20)
        
        if similar_aps:
            batch_frame = ttk.LabelFrame(dialog, text="Apply to Similar APs", padding=10)
            batch_frame.pack(fill=tk.X, padx=20, pady=10)
            
            ttk.Label(batch_frame, 
                     text=f"Found {len(similar_aps)} APs with similar morphology.",
                     font=("Helvetica", 10)).pack(anchor='w', pady=2)
            
            ttk.Label(batch_frame, 
                     text="APs with >95% similarity will be automatically selected.",
                     font=("Helvetica", 9, "italic")).pack(anchor='w', pady=2)
            
            self.batch_apply_var = tk.BooleanVar(value=True)
            ttk.Checkbutton(batch_frame, 
                          text=f"Apply this correction to similar APs (selective)",
                          variable=self.batch_apply_var).pack(anchor='w', pady=5)
        
        button_frame = ttk.Frame(dialog)
        button_frame.pack(pady=20)
        
        def apply_correction():
            trace_id = dat.get('trace_id')
            
            self.clear_correction_of_type(self.current_trace_index, current_ap_idx, 'late_repol')
            
            current_ap['APD80_raw'] = raw_apd80
            current_ap['APD90_raw'] = raw_apd90
            current_ap['APD80'] = corrected_apd80
            current_ap['APD90'] = corrected_apd90
            current_ap['has_bump'] = True
            current_ap['late_repolarization_corrected'] = True
            current_ap['has_late_repol'] = True
            
            current_type = current_ap.get('correction_type', 'auto')
            if current_type == 'auto':
                current_ap['correction_type'] = 'late_repol'
            elif 'late_repol' not in current_type:
                current_ap['correction_type'] = f'{current_type}+late_repol'
            
            current_ap['bump_fit_slope'] = slope
            current_ap['bump_fit_intercept'] = intercept
            current_ap['bump_fit_range'] = fit_range
            
            if trace_id not in self.late_repolarization_corrections:
                self.late_repolarization_corrections[trace_id] = {}
            self.late_repolarization_corrections[trace_id][current_ap_idx] = True
            
            apd50 = current_ap.get('APD50', np.nan)
            if not math.isnan(apd50) and corrected_apd90 > 0:
                current_ap['Repolarization_Fraction'] = (corrected_apd90 - apd50) / corrected_apd90
            
            if hasattr(self, 'batch_apply_var') and self.batch_apply_var.get() and similar_aps:
                current_trace_info = {
                    'file_name': dat.get('file_name', 'unknown'),
                    'cell_id': dat.get('cell_id', 'unknown'),
                    'frequency': dat.get('frequency', 'unknown')
                }
    
                selective_dialog = SelectiveBatchCorrectionDialog(
                    self.root, 'late_repolarization', current_ap, similar_aps,
                    current_trace_info, self.get_ap_display_info
                )
                selective_dialog.wait_window()
    
                selected_pairs = selective_dialog.get_selected_pairs()
                if selected_pairs:
                    total = len(selected_pairs)
                    progress_dialog = BatchProgressDialog(self.root, "Applying Late Repolarization Correction", total)
        
                    for i, (sim_trace_idx, sim_ap_idx) in enumerate(selected_pairs):
                        if progress_dialog.is_cancelled():
                            break
            
                        status_text = f"Correcting {i+1} of {total}: AP at trace {sim_trace_idx + 1}"
                        progress_dialog.update(i + 1, status_text)
            
                        sim_trace = self.all_results[sim_trace_idx]
                        sim_ap = sim_trace['ap_metrics'][sim_ap_idx]
                        sim_trace_id = sim_trace.get('trace_id')
            
                        self.clear_correction_of_type(sim_trace_idx, sim_ap_idx, 'late_repol')
            
                        rmp_sim = sim_ap.get('RMP', np.nan)
                        peak_idx_sim = sim_ap.get('peak_idx', 0)
                        if peak_idx_sim < len(sim_trace['voltage_smooth']):
                            peak_v_sim = sim_trace['voltage_smooth'][peak_idx_sim]
                        else:
                            peak_v_sim = np.nan
            
                        corr80, corr90, slope_sim, intercept_sim, fit_range_sim = compute_corrected_apd_from_fit_v2(
                            sim_trace['time'], sim_trace['voltage_smooth'], 
                            peak_idx_sim, rmp_sim, peak_v_sim
                        )
            
                        if corr80 and corr90:
                            if sim_trace_id not in self.late_repolarization_corrections:
                                self.late_repolarization_corrections[sim_trace_id] = {}
                            self.late_repolarization_corrections[sim_trace_id][sim_ap_idx] = True
                
                            sim_ap['APD80_raw'] = sim_ap.get('APD80', np.nan)
                            sim_ap['APD90_raw'] = sim_ap.get('APD90', np.nan)
                            sim_ap['APD80'] = corr80
                            sim_ap['APD90'] = corr90
                            sim_ap['has_bump'] = True
                            sim_ap['late_repolarization_corrected'] = True
                            sim_ap['has_late_repol'] = True
                            
                            sim_current_type = sim_ap.get('correction_type', 'auto')
                            if sim_current_type == 'auto':
                                sim_ap['correction_type'] = 'late_repol'
                            elif 'late_repol' not in sim_current_type:
                                sim_ap['correction_type'] = f'{sim_current_type}+late_repol'
                            
                            sim_ap['bump_fit_slope'] = slope_sim
                            sim_ap['bump_fit_intercept'] = intercept_sim
                            sim_ap['bump_fit_range'] = fit_range_sim
                
                            apd50_sim = sim_ap.get('APD50', np.nan)
                            if not math.isnan(apd50_sim) and corr90 > 0:
                                sim_ap['Repolarization_Fraction'] = (corr90 - apd50_sim) / corr90
        
                    progress_dialog.close()
        
                    messagebox.showinfo("Batch Correction Complete", 
                                    f"Successfully corrected {len(selected_pairs)} APs")
            
            self.update_results_table()
            self.plot_current_trace()
            
            dialog.destroy()
            messagebox.showinfo("Correction Applied",
                              "Late repolarization correction has been applied to this AP.\n"
                              "The corrected values will be used in exports.")
        
        ttk.Button(button_frame, text="Apply Correction", command=apply_correction, width=20).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=dialog.destroy, width=15).pack(side=tk.LEFT, padx=5)
    
    def plot_current_trace(self):
        if not self.all_results:
            self.ax.clear()
            self.ax.text(0.5, 0.5, "No traces to display", ha='center', va='center', transform=self.ax.transAxes)
            self.canvas.draw()
            return
    
        idx = self.current_trace_index
        dat = self.all_results[idx]
        t = dat['time']
        v_s = dat['voltage_smooth']
        ap_metrics = dat.get('ap_metrics', [])
        species = dat.get('species', 'default')
    
        self.ax.clear()
    
        if not self.yaxis_auto.get() and self.visual_filter_only.get():
            y_min = self.yaxis_min.get()
            y_max = self.yaxis_max.get()
        
            visible_mask = (v_s >= y_min) & (v_s <= y_max)
            if np.any(visible_mask):
                self.ax.plot(t[visible_mask], v_s[visible_mask], 'b-', linewidth=2, label='Visible trace')
                out_of_range = ~visible_mask
                if np.any(out_of_range):
                    self.ax.plot(t[out_of_range], v_s[out_of_range], 'b-', linewidth=1, alpha=0.3,
                            label='Out of view')
            else:
                self.ax.plot(t, v_s, 'b-', linewidth=2, label='Trace')
        else:
            self.ax.plot(t, v_s, 'b-', linewidth=2, label='Trace')
    
        print(f"\nPlotting trace {idx}: {len(ap_metrics)} APs found")
    
        for m_idx, m in enumerate(ap_metrics):
            pidx = m['peak_idx']
            pt = m['peak_time']
            pv = v_s[pidx] if pidx < len(v_s) else np.nan
        
            has_manual_peak = m.get('has_manual_correction', False)
            has_manual_upstroke = m.get('has_manual_upstroke', False)
            has_late_repol = m.get('late_repolarization_corrected', False)
        
            print(f"  AP {m_idx}: peak at {pt:.1f}ms, correction_type={m.get('correction_type', 'auto')}, manual_peak={has_manual_peak}")
        
            if has_manual_peak:
                marker_style = 'D'
                marker_color = 'lime'
                marker_label = 'Manual Peak' if m_idx == 0 else ""
                marker_size = 12
            elif has_late_repol:
                marker_style = 's'
                marker_color = 'orange'
                marker_label = 'Late Repol Corrected' if m_idx == 0 else ""
                marker_size = 10
            else:
                marker_style = 'o'
                marker_color = 'green'
                marker_label = 'Auto-detected Peak' if m_idx == 0 else ""
                marker_size = 10
        
            self.ax.plot(pt, pv, marker_style, markersize=marker_size, 
                        markeredgecolor='darkgreen',
                        markerfacecolor=marker_color, 
                        label=marker_label)
        
            rmp = m.get('RMP', np.nan)
            if not math.isnan(rmp):
                self.ax.axhline(y=rmp, color='black', linestyle='--', alpha=0.8, linewidth=1.5)
                self.ax.text(t[0] + 10, rmp + 1, f'RMP: {rmp:.1f} mV',
                            fontsize=9, ha='left', va='bottom', fontweight='bold',
                            bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.8))
        
            onset_idx = m.get('onset_idx')
            if not math.isnan(onset_idx) and int(onset_idx) < len(t):
                onset_time = t[int(onset_idx)]
                onset_voltage = v_s[int(onset_idx)]
            
                self.ax.axvline(x=onset_time, color='cyan', linestyle='--', alpha=0.6, linewidth=1)
            
                if has_manual_upstroke:
                    upstroke_marker = 'D'
                    upstroke_color = 'blue'
                    upstroke_label = 'Manual Upstroke' if m_idx == 0 else ""
                else:
                    upstroke_marker = 'o'
                    upstroke_color = 'cyan'
                    upstroke_label = 'Auto Upstroke' if m_idx == 0 else ""
            
                self.ax.plot(onset_time, onset_voltage, upstroke_marker, markersize=8,
                            markeredgecolor='darkcyan', markerfacecolor=upstroke_color,
                            label=upstroke_label)
            
                upstroke_duration = m['peak_time'] - onset_time
                self.ax.text(onset_time + 5, onset_voltage + 5, f'Upstroke: {upstroke_duration:.2f} ms',
                            fontsize=8, color='cyan', alpha=0.8)
            
                self.ax.plot([onset_time, pt], [onset_voltage, pv], 'c--', linewidth=1.5,
                            alpha=0.7, label='Upstroke' if m_idx == 0 else "")
        
            dvdt_max_idx = m.get('dvdt_max_idx')
            if not math.isnan(dvdt_max_idx) and int(dvdt_max_idx) < len(t):
                dvdt_time = t[int(dvdt_max_idx)]
                dvdt_voltage = v_s[int(dvdt_max_idx)]
                self.ax.plot(dvdt_time, dvdt_voltage, 'r*', markersize=12,
                            label='dV/dt max' if m_idx == 0 else "")
            
                dvdt_max_val = m.get('dVdt_max', np.nan)
                if not math.isnan(dvdt_max_val):
                    self.ax.text(dvdt_time, dvdt_voltage + 5, f'dV/dt: {dvdt_max_val:.1f} mV/ms',
                            fontsize=8, ha='center', va='bottom')
        
            if has_late_repol:
                slope = m.get('bump_fit_slope')
                intercept = m.get('bump_fit_intercept')
                fit_range = m.get('bump_fit_range')
            
                if slope is not None and intercept is not None and fit_range:
                    t_start, t_end = fit_range
                
                    t_fit = np.linspace(t_start, t_end, 100)
                    v_fit = slope * t_fit + intercept
                    self.ax.plot(t_fit, v_fit, 'orange', linewidth=2.5, linestyle='-',
                            alpha=0.9, label='Linear fit (APD50-APD70)' if m_idx == 0 else "")
                
                    peak_time = m['peak_time']
                    rmp_val = m['RMP']
                    peak_v_val = v_s[m['peak_idx']] if m['peak_idx'] < len(v_s) else np.nan
                    apa_val = peak_v_val - rmp_val if not math.isnan(peak_v_val) and not math.isnan(rmp_val) else 100
                
                    v80 = rmp_val + 0.2 * apa_val
                    v90 = rmp_val + 0.1 * apa_val
                
                    t80 = (v80 - intercept) / slope if slope != 0 else None
                    t90 = (v90 - intercept) / slope if slope != 0 else None
                
                    if t80 is not None and t80 > t_end and t80 < t[-1]:
                        t_extend = np.linspace(t_end, min(t80, t[-1]), 50)
                        v_extend = slope * t_extend + intercept
                        self.ax.plot(t_extend, v_extend, 'orange', linewidth=1.5, linestyle=':', alpha=0.8)
                        self.ax.plot(t80, v80, 'go', markersize=10,
                                markerfacecolor='green', markeredgecolor='darkgreen',
                                label='Corrected APD80' if m_idx == 0 else "")
                        self.ax.text(t80 + 5, v80, f'APD80: {m["APD80"]:.1f} ms',
                                fontsize=8, color='green')
                
                    if t90 is not None and t90 > t_end and t90 < t[-1]:
                        t_extend = np.linspace(max(t_end, t80) if t80 else t_end, min(t90, t[-1]), 50)
                        v_extend = slope * t_extend + intercept
                        self.ax.plot(t_extend, v_extend, 'orange', linewidth=1.5, linestyle=':', alpha=0.8)
                        self.ax.plot(t90, v90, 'g*', markersize=12,
                                markerfacecolor='lime', markeredgecolor='darkgreen',
                                label='Corrected APD90' if m_idx == 0 else "")
                        self.ax.text(t90 + 5, v90, f'APD90: {m["APD90"]:.1f} ms',
                                fontsize=8, color='green')
        
            if not math.isnan(rmp) and not math.isnan(pv):
                apa = pv - rmp
                apd_colors = plt.cm.viridis(np.linspace(0.2, 0.9, len(APD_PERCENTAGES)))
            
                for percent_idx, percent in enumerate(APD_PERCENTAGES):
                    level = rmp + (1 - percent / 100) * apa
                    y_min_curr, y_max_curr = self.ax.get_ylim()
                    if y_min_curr <= level <= y_max_curr:
                        crossing_time = find_crossing_time(t, v_s, m['peak_idx'], level)
                        if crossing_time:
                            self.ax.axhline(y=level, color=apd_colors[percent_idx],
                                        linestyle='--', alpha=0.5, linewidth=1)
                            self.ax.axvline(x=crossing_time, color=apd_colors[percent_idx],
                                        linestyle=':', alpha=0.5, linewidth=1)
                            if percent in [10, 50, 90]:
                                self.ax.text(crossing_time + 5, level,
                                        f'APD{percent}: {(crossing_time - pt):.1f} ms',
                                        fontsize=7, color=apd_colors[percent_idx], alpha=0.8)
    
        if self.sync_zoom.get() and self.current_xlim and self.current_ylim:
            self.ax.set_xlim(self.current_xlim)
            self.ax.set_ylim(self.current_ylim)
        else:
            frequency = dat.get('frequency', '')
            if frequency in FREQUENCY_XLIMITS:
                self.ax.set_xlim(0, FREQUENCY_XLIMITS[frequency])
            else:
                self.ax.set_xlim(0, 1000)
        
            if self.yaxis_auto.get():
                filter_outliers = self.filter_outliers.get()
                y_min, y_max = detect_voltage_range_enhanced(v_s, species, filter_outliers)
            else:
                y_min = self.yaxis_min.get()
                y_max = self.yaxis_max.get()
        
            self.ax.set_ylim(y_min, y_max)
    
        self.ax.set_xlabel("Time (ms)", fontsize=11)
        self.ax.set_ylabel("Voltage (mV)", fontsize=11)
    
        title = f"Trace {idx + 1}/{len(self.all_results)}"
        if dat.get('file_name'):
            title += f" - {dat['file_name']}"
    
        if dat.get('dual_path_used', False):
            title += " [Dual-Path Detection]"
    
        if self.use_corrected_apd.get():
            title += " [Corrected APD80/90]"
        
        if dat.get('adaptive_smoothing_used', False):
            title += f" [Adaptive Smoothing: {dat.get('smoothing_ms_used', 1.5):.1f}ms]"
        
        # Show immature mode indicator if active
        if dat.get('immature_mode_used', False):
            title += " [Cardioid Immature Mode]"
        
        if dat.get('ap_metrics'):
            dvdt_max = dat['ap_metrics'][0].get('dVdt_max', np.nan)
            species = dat.get('species', 'default')
            if not math.isnan(dvdt_max):
                warnings_list = validate_dvdt_max(dvdt_max, species, dat.get('smoothing_ms_used', 1.5), dat.get('sampling_rate_hz', 1000))
                if any('BELOW' in w or 'ABOVE' in w for w in warnings_list):
                    title += " ⚠"
    
        trace_id = dat.get('trace_id')
        if trace_id in self.validated_traces:
            title += " ✓"
    
        self.ax.set_title(title, fontsize=12, fontweight='bold')
        self.ax.legend(loc='upper right', fontsize=8, ncol=2)
        self.ax.grid(True, alpha=0.3)
    
        self.canvas.draw()
    
    def on_yaxis_auto_toggle(self):
        if self.yaxis_auto.get():
            self.yaxis_min_entry.config(state='disabled')
            self.yaxis_max_entry.config(state='disabled')
        else:
            self.yaxis_min_entry.config(state='normal')
            self.yaxis_max_entry.config(state='normal')
    
    def apply_yaxis_range(self):
        if self.all_results:
            self.plot_current_trace()
    
    def auto_detect_yaxis_range(self):
        if not self.all_results:
            return
        
        dat = self.all_results[self.current_trace_index]
        voltage = dat['voltage_smooth']
        
        species = dat.get('species', 'default')
        if self.selected_species.get() != 'auto':
            species = self.selected_species.get()
        
        filter_outliers = self.filter_outliers.get()
        y_min, y_max = detect_voltage_range_enhanced(voltage, species, filter_outliers)
        
        self.yaxis_min.set(round(y_min, 1))
        self.yaxis_max.set(round(y_max, 1))
        
        self.yaxis_auto.set(False)
        self.on_yaxis_auto_toggle()
        
        self.plot_current_trace()
        
        messagebox.showinfo("Y-axis Detection",
                            f"Auto-detected Y-axis range for {species}:\n"
                            f"Min: {y_min:.1f} mV, Max: {y_max:.1f} mV\n"
                            f"Visual filtering: {'Enabled' if self.visual_filter_only.get() else 'Disabled'}")
    
    def on_draw_event(self, event):
        if self.ax and self.sync_zoom.get():
            self.current_xlim = self.ax.get_xlim()
            self.current_ylim = self.ax.get_ylim()
    
    def update_results_table(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        
        row_index = 0
        for res in self.all_results:
            trace_id = res.get('trace_id')
            if trace_id and self.rejection_manager.is_rejected(trace_id):
                continue
            
            file = res.get('file_name', '')
            cell = res.get('display_cell_id', res.get('cell_id', ''))
            freq = res.get('frequency', '')
            drug = res.get('drug', 'None')
            concentration = res.get('concentration', '')
            range_name = res.get('range_name', '')
            species = res.get('species', 'default')
            stv = res.get('stv_apd90', np.nan)
            
            for m in res.get('ap_metrics', []):
                correction_parts = []
                if m.get('has_manual_correction', False):
                    correction_parts.append('Peak')
                if m.get('has_manual_upstroke', False):
                    correction_parts.append('Upstroke')
                if m.get('has_late_repol', False):
                    correction_parts.append('LateRepol')
                
                correction_display = '+'.join(correction_parts) if correction_parts else 'Auto'
                
                drug_info = drug
                if concentration:
                    drug_info += f" ({concentration})"
                
                dvdt_max = m.get('dVdt_max', np.nan)
                rmp = m.get('RMP', np.nan)
                apd30 = m.get('APD30', np.nan)
                apd50 = m.get('APD50', np.nan)
                apd90 = m.get('APD90', np.nan)
                apa = m.get('APA', np.nan)
                repol_frac = m.get('Repolarization_Fraction', np.nan)
                
                is_validated = "✓" if trace_id in self.validated_traces else ""
                
                self.tree.insert('', tk.END, iid=f"I{row_index}", values=(
                    is_validated,
                    file,
                    cell,
                    freq,
                    drug_info,
                    range_name,
                    species,
                    correction_display,
                    f"{apa:.2f}" if not math.isnan(apa) else "N/A",
                    f"{apd30:.1f}" if not math.isnan(apd30) else "N/A",
                    f"{apd50:.1f}" if not math.isnan(apd50) else "N/A",
                    f"{apd90:.1f}" if not math.isnan(apd90) else "N/A",
                    f"{dvdt_max:.1f}",
                    f"{rmp:.1f}",
                    f"{stv:.3f}" if not math.isnan(stv) else "N/A",
                    f"{repol_frac:.3f}" if not math.isnan(repol_frac) else "N/A"
                ))
                row_index += 1
        
        self.stats_text.delete('1.0', tk.END)
        
        if self.all_results:
            all_apd10 = []
            all_apd20 = []
            all_apd30 = []
            all_apd40 = []
            all_apd50 = []
            all_apd60 = []
            all_apd70 = []
            all_apd80 = []
            all_apd90 = []
            all_apd95 = []
            all_apa = []
            all_dvdt = []
            all_rmp = []
            all_stv = []
            all_repol_frac = []
            
            for res in self.all_results:
                for ap in res.get('ap_metrics', []):
                    apd10 = ap.get('APD10')
                    apd20 = ap.get('APD20')
                    apd30 = ap.get('APD30')
                    apd40 = ap.get('APD40')
                    apd50 = ap.get('APD50')
                    apd60 = ap.get('APD60')
                    apd70 = ap.get('APD70')
                    apd80 = ap.get('APD80')
                    apd90 = ap.get('APD90')
                    apd95 = ap.get('APD95')
                    apa = ap.get('APA')
                    dvdt = ap.get('dVdt_max')
                    rmp = ap.get('RMP')
                    repol_frac = ap.get('Repolarization_Fraction')
                    
                    if apd10 and not math.isnan(apd10):
                        all_apd10.append(apd10)
                    if apd20 and not math.isnan(apd20):
                        all_apd20.append(apd20)
                    if apd30 and not math.isnan(apd30):
                        all_apd30.append(apd30)
                    if apd40 and not math.isnan(apd40):
                        all_apd40.append(apd40)
                    if apd50 and not math.isnan(apd50):
                        all_apd50.append(apd50)
                    if apd60 and not math.isnan(apd60):
                        all_apd60.append(apd60)
                    if apd70 and not math.isnan(apd70):
                        all_apd70.append(apd70)
                    if apd80 and not math.isnan(apd80):
                        all_apd80.append(apd80)
                    if apd90 and not math.isnan(apd90):
                        all_apd90.append(apd90)
                    if apd95 and not math.isnan(apd95):
                        all_apd95.append(apd95)
                    if apa and not math.isnan(apa):
                        all_apa.append(apa)
                    if dvdt and not math.isnan(dvdt):
                        all_dvdt.append(dvdt)
                    if rmp and not math.isnan(rmp):
                        all_rmp.append(rmp)
                    if repol_frac and not math.isnan(repol_frac):
                        all_repol_frac.append(repol_frac)
                
                stv_val = res.get('stv_apd90')
                if stv_val and not math.isnan(stv_val):
                    all_stv.append(stv_val)
            
            if all_apd10:
                stats_text = f"SUMMARY STATISTICS\n"
                stats_text += f"{'=' * 40}\n"
                stats_text += f"Total Valid APs: {len(all_apd10)}\n"
                stats_text += f"Validated traces: {len(self.validated_traces)}\n\n"
                stats_text += f"RMP measured from baseline (first 10 ms) - No automatic correction\n"
                stats_text += f"dV/dt_max (improved Savitzky-Golay method with minimal upstroke smoothing)\n"
                stats_text += f"Corrected APD80/90 using APD50-APD70 linear fit\n"
                stats_text += f"Repolarization Fraction: (APD90 - APD50)/APD90\n\n"
                
                apd_stats = [
                    ("Parameter", "Mean ± SEM", "Range", "n"),
                    ("APD10", f"{np.mean(all_apd10):.1f} ± {np.std(all_apd10) / np.sqrt(len(all_apd10)) if len(all_apd10) > 1 else 0:.1f} ms",
                     f"{min(all_apd10):.1f} - {max(all_apd10):.1f} ms", str(len(all_apd10))),
                    ("APD20", f"{np.mean(all_apd20):.1f} ± {np.std(all_apd20) / np.sqrt(len(all_apd20)) if len(all_apd20) > 1 else 0:.1f} ms" if all_apd20 else "N/A",
                     f"{min(all_apd20):.1f} - {max(all_apd20):.1f} ms" if all_apd20 else "N/A", str(len(all_apd20)) if all_apd20 else "0"),
                    ("APD30", f"{np.mean(all_apd30):.1f} ± {np.std(all_apd30) / np.sqrt(len(all_apd30)) if len(all_apd30) > 1 else 0:.1f} ms" if all_apd30 else "N/A",
                     f"{min(all_apd30):.1f} - {max(all_apd30):.1f} ms" if all_apd30 else "N/A", str(len(all_apd30)) if all_apd30 else "0"),
                    ("APD50", f"{np.mean(all_apd50):.1f} ± {np.std(all_apd50) / np.sqrt(len(all_apd50)) if len(all_apd50) > 1 else 0:.1f} ms" if all_apd50 else "N/A",
                     f"{min(all_apd50):.1f} - {max(all_apd50):.1f} ms" if all_apd50 else "N/A", str(len(all_apd50)) if all_apd50 else "0"),
                    ("APD80", f"{np.mean(all_apd80):.1f} ± {np.std(all_apd80) / np.sqrt(len(all_apd80)) if len(all_apd80) > 1 else 0:.1f} ms" if all_apd80 else "N/A",
                     f"{min(all_apd80):.1f} - {max(all_apd80):.1f} ms" if all_apd80 else "N/A", str(len(all_apd80)) if all_apd80 else "0"),
                    ("APD90", f"{np.mean(all_apd90):.1f} ± {np.std(all_apd90) / np.sqrt(len(all_apd90)) if len(all_apd90) > 1 else 0:.1f} ms" if all_apd90 else "N/A",
                     f"{min(all_apd90):.1f} - {max(all_apd90):.1f} ms" if all_apd90 else "N/A", str(len(all_apd90)) if all_apd90 else "0"),
                    ("APD95", f"{np.mean(all_apd95):.1f} ± {np.std(all_apd95) / np.sqrt(len(all_apd95)) if len(all_apd95) > 1 else 0:.1f} ms" if all_apd95 else "N/A",
                     f"{min(all_apd95):.1f} - {max(all_apd95):.1f} ms" if all_apd95 else "N/A", str(len(all_apd95)) if all_apd95 else "0"),
                    ("", "", "", ""),
                    ("APA", f"{np.mean(all_apa):.1f} ± {np.std(all_apa) / np.sqrt(len(all_apa)) if len(all_apa) > 1 else 0:.1f} mV" if all_apa else "N/A",
                     f"{min(all_apa):.1f} - {max(all_apa):.1f} mV" if all_apa else "N/A", str(len(all_apa)) if all_apa else "0"),
                    ("dV/dt max", f"{np.mean(all_dvdt):.1f} ± {np.std(all_dvdt) / np.sqrt(len(all_dvdt)) if len(all_dvdt) > 1 else 0:.1f} mV/ms" if all_dvdt else "N/A",
                     f"{min(all_dvdt):.1f} - {max(all_dvdt):.1f} mV/ms" if all_dvdt else "N/A", str(len(all_dvdt)) if all_dvdt else "0"),
                    ("RMP", f"{np.mean(all_rmp):.1f} ± {np.std(all_rmp) / np.sqrt(len(all_rmp)) if len(all_rmp) > 1 else 0:.1f} mV" if all_rmp else "N/A",
                     f"{min(all_rmp):.1f} - {max(all_rmp):.1f} mV" if all_rmp else "N/A", str(len(all_rmp)) if all_rmp else "0"),
                    ("STV", f"{np.mean(all_stv):.3f} ± {np.std(all_stv) / np.sqrt(len(all_stv)) if len(all_stv) > 1 else 0:.3f}" if all_stv else "N/A",
                     f"{min(all_stv):.3f} - {max(all_stv):.3f}" if all_stv else "N/A", str(len(all_stv)) if all_stv else "0"),
                    ("Repol Frac", f"{np.mean(all_repol_frac):.3f} ± {np.std(all_repol_frac) / np.sqrt(len(all_repol_frac)) if len(all_repol_frac) > 1 else 0:.3f}" if all_repol_frac else "N/A",
                     f"{min(all_repol_frac):.3f} - {max(all_repol_frac):.3f}" if all_repol_frac else "N/A", str(len(all_repol_frac)) if all_repol_frac else "0")
                ]
                
                col_widths = [15, 25, 25, 10]
                for row in apd_stats:
                    line = ""
                    for i, cell in enumerate(row):
                        line += str(cell).ljust(col_widths[i])
                    stats_text += line + "\n"
                
                self.stats_text.insert(tk.END, stats_text)
    
    def prev_trace(self):
        if not self.all_results:
            return
        new_index = self.current_trace_index - 1
        while new_index >= 0:
            current_trace = self.all_results[new_index]
            trace_id = current_trace.get('trace_id')
            if not trace_id or not self.rejection_manager.is_rejected(trace_id):
                self.current_trace_index = new_index
                self.plot_current_trace()
                return
            new_index -= 1
        messagebox.showinfo("Navigation", "Reached beginning of trace list")
    
    def next_trace(self):
        if not self.all_results:
            return
        new_index = self.current_trace_index + 1
        while new_index < len(self.all_results):
            current_trace = self.all_results[new_index]
            trace_id = current_trace.get('trace_id')
            if not trace_id or not self.rejection_manager.is_rejected(trace_id):
                self.current_trace_index = new_index
                self.plot_current_trace()
                return
            new_index += 1
        messagebox.showinfo("Navigation", "Reached end of trace list")
    
    def validate_current_trace(self):
        if not self.all_results:
            return
        
        dat = self.all_results[self.current_trace_index]
        trace_id = dat.get('trace_id')
        
        if trace_id in self.validated_traces:
            self.validated_traces.remove(trace_id)
            messagebox.showinfo("Validation", "Trace validation removed")
        else:
            self.validated_traces.add(trace_id)
            messagebox.showinfo("Validation", "Trace validated")
        
        self.update_results_table()
        self.plot_current_trace()
    
    def validate_all_traces(self):
        self.validated_traces.clear()
        for res in self.all_results:
            trace_id = res.get('trace_id')
            if trace_id and not self.rejection_manager.is_rejected(trace_id):
                self.validated_traces.add(trace_id)
        
        self.update_results_table()
        messagebox.showinfo("Validation", f"Validated all {len(self.validated_traces)} traces")
    
    def on_tree_select(self, event):
        item = self.tree.identify_row(event.y)
        if item:
            values = self.tree.item(item)['values']
            if values and len(values) > 0:
                current_validation = values[0]
                trace_index = int(item[1:]) if item.startswith('I') else int(item)
                
                if current_validation == "✓":
                    self.tree.set(item, "Validate", "")
                    if trace_index < len(self.all_results):
                        trace_id = self.all_results[trace_index].get('trace_id')
                        self.validated_traces.discard(trace_id)
                else:
                    self.tree.set(item, "Validate", "✓")
                    if trace_index < len(self.all_results):
                        trace_id = self.all_results[trace_index].get('trace_id')
                        self.validated_traces.add(trace_id)
    
    def flag_current_trace(self):
        if not self.all_results:
            return
        dat = self.all_results[self.current_trace_index]
        file = dat.get('file')
        meta = self.parsed_files.get(file, {})
        meta['flagged'] = True
        self.parsed_files[file] = meta
        messagebox.showinfo("Flagged", f"Marked {Path(file).name} as problematic.")
    
    def reject_current_trace(self):
        if not self.all_results:
            return
        dat = self.all_results[self.current_trace_index]
        trace_id = dat.get('trace_id')
        if not trace_id:
            return
        
        reason = self.rejection_reason_var.get()
        
        self.rejection_manager.reject_trace(trace_id, reason)
        self.next_trace()
    
    def add_files_dialog(self):
        files = filedialog.askopenfilenames(
            title="Select CSV/Excel files",
            filetypes=[
                ("CSV and Excel files", "*.csv;*.xlsx;*.xls"),
                ("CSV files", "*.csv"),
                ("Excel files", "*.xlsx;*.xls"),
                ("All files", "*.*")
            ]
        )
        
        if files:
            for f in files:
                if f not in self.file_list:
                    self.file_list.append(f)
                    
                    filename = Path(f).name
                    
                    # Try PatchMaster extraction first
                    pm_meta = extract_patchmaster_metadata(filename)
                    cell_id = pm_meta['cell_id']
                    frequency = pm_meta['frequency']
                    drug = pm_meta['drug']
                    species = detect_species_from_filename(filename)
                    
                    self.file_metadata[f] = {
                        'cell_id': cell_id,
                        'display_cell_id': cell_id,
                        'frequency': frequency if frequency else '1.0',
                        'drug': drug,
                        'concentration': '',
                        'species': species,
                        'range_name': filename,
                        'source': 'PatchMaster' if pm_meta['source'] == 'PatchMaster' else 'CSV'
                    }
                    
                    try:
                        # Try PatchMaster parser first
                        time_arr, volt_arr, pm_meta_data = parse_patchmaster_csv(f)
                        if time_arr is not None and volt_arr is not None:
                            self.parsed_files[f] = {
                                'type': 'csv/excel',
                                'time': time_arr,
                                'voltage': volt_arr,
                                'source': 'PatchMaster'
                            }
                        else:
                            if f.endswith('.csv'):
                                df = pd.read_csv(f, nrows=100)
                            else:
                                df = pd.read_excel(f, nrows=100)
                            
                            tcol, vcol = fuzzy_find_columns(df)
                            self.parsed_files[f] = {
                                'type': 'csv/excel',
                                'columns': list(df.columns),
                                'time_col': tcol,
                                'voltage_col': vcol,
                                'n_rows': len(df)
                            }
                    except Exception as e:
                        print(f"Error parsing {f}: {e}")
                        self.parsed_files[f] = {'type': 'unknown'}
            
            self.update_file_list_display()
    
    def add_abf_files_dialog(self):
        if not ABF_AVAILABLE:
            messagebox.showerror("ABF Support Not Available",
                                 "pyabf library is not installed.\n\n"
                                 "Install it using: pip install pyabf\n"
                                 "ABF file support will be disabled.")
            return
        
        files = filedialog.askopenfilenames(
            title="Select ABF files",
            filetypes=[("ABF files", "*.abf"), ("All files", "*.*")]
        )
        
        if files:
            for f in files:
                if f not in self.file_list:
                    try:
                        abf = pyabf.ABF(f)
                        sweep_count = abf.sweepCount
                        
                        dialog = ABFRangeSelectionDialog(self.root, f, sweep_count)
                        dialog.wait_window()
                        
                        selected_ranges = dialog.get_ranges()
                        
                        if selected_ranges is None:
                            continue
                        
                        self.file_list.append(f)
                        self.abf_trace_selections[f] = selected_ranges
                        
                        filename = Path(f).name
                        cell_id, frequency = extract_metadata_from_filename(filename)
                        species = detect_species_from_filename(filename)
                        
                        self.file_metadata[f] = {
                            'cell_id': cell_id,
                            'display_cell_id': cell_id,
                            'frequency': frequency if frequency else '1.0',
                            'drug': 'None',
                            'concentration': '',
                            'species': species,
                            'range_name': filename,
                            'sweep_count': sweep_count,
                            'selected_ranges': len(selected_ranges) if selected_ranges else 1
                        }
                        
                        self.parsed_files[f] = {
                            'type': 'abf',
                            'sweep_count': sweep_count,
                            'selected_ranges': selected_ranges,
                            'ranges_info': selected_ranges if selected_ranges else [{
                                'name': 'All',
                                'range': (0, sweep_count - 1),
                                'drug': 'None',
                                'concentration': '',
                                'description': 'All sweeps'
                            }]
                        }
                        
                    except Exception as e:
                        print(f"Error processing ABF file {f}: {e}")
                        traceback.print_exc()
                        messagebox.showerror("ABF Error", f"Could not read ABF file:\n{f}\n\nError: {str(e)}")
            
            self.update_file_list_display()
    
    def show_enhanced_stacking(self):
        if not self.file_list:
            messagebox.showwarning("No Files", "Please add files first to use stacking.")
            return
        
        stackable_files = [f for f in self.file_list if not f.endswith('.abf')]
        
        if not stackable_files:
            messagebox.showwarning("No Stackable Files",
                                   "Stacking is available only for CSV/Excel files.\n"
                                   "ABF files cannot be directly stacked.")
            return
        
        dialog = EnhancedExcelStackerDialog(self.root, stackable_files, self.file_metadata)
        dialog.wait_window()
        
        result = dialog.result
        
        if result and result.get("stacked_data"):
            self.stacked_files.update(result["stacked_data"])
            
            for group_name, data in result["stacked_data"].items():
                self.file_metadata[f"Stacked_{group_name}"] = {
                    'cell_id': data.get('cell_id', group_name),
                    'display_cell_id': data.get('cell_id', group_name),
                    'frequency': data.get('frequency', 'Multiple'),
                    'drug': data.get('drug', 'None'),
                    'concentration': data.get('concentration', ''),
                    'species': 'default',
                    'range_name': group_name,
                    'stacked': True,
                    'n_traces': data.get('n_traces', 0)
                }
            
            self.update_file_list_display()
            
            messagebox.showinfo("Stacking Complete",
                                f"Successfully stacked {len(result['stacked_data'])} groups.\n"
                                f"Stacked files are now available for analysis.")
    
    def remove_selected_file(self):
        selection = self.file_listbox.selection()
        if not selection:
            return
        
        for item in selection:
            values = self.file_listbox.item(item)['values']
            if values:
                filename = values[0]
                
                for f in self.file_list:
                    if Path(f).name == filename:
                        self.file_list.remove(f)
                        if f in self.file_metadata:
                            del self.file_metadata[f]
                        if f in self.parsed_files:
                            del self.parsed_files[f]
                        if f in self.abf_trace_selections:
                            del self.abf_trace_selections[f]
                        break
                
                for stacked_name in list(self.stacked_files.keys()):
                    if f"Stacked_{stacked_name}" == filename:
                        del self.stacked_files[stacked_name]
                        if f"Stacked_{stacked_name}" in self.file_metadata:
                            del self.file_metadata[f"Stacked_{stacked_name}"]
                        break
        
        self.update_file_list_display()
    
    def clear_all_files(self):
        if not self.file_list and not self.stacked_files:
            return
        
        response = messagebox.askyesno("Clear All Files",
                                       "Are you sure you want to clear all files?\n"
                                       "This will remove all loaded files and stacked data.")
        
        if response:
            self.file_list.clear()
            self.stacked_files.clear()
            self.file_metadata.clear()
            self.parsed_files.clear()
            self.abf_trace_selections.clear()
            self.all_results.clear()
            self.validated_traces.clear()
            self.analyzed_trace_ids.clear()
            self.manual_peak_corrections.clear()
            self.manual_upstroke_corrections.clear()
            self.late_repolarization_corrections.clear()
            
            self.update_file_list_display()
            self.update_results_table()
            
            self.ax.clear()
            self.ax.text(0.5, 0.5, "No files loaded",
                         ha='center', va='center', transform=self.ax.transAxes)
            self.canvas.draw()
    
    def choose_output_folder(self):
        folder = filedialog.askdirectory(
            title="Select Output Folder",
            initialdir=str(self.output_folder)
        )
        
        if folder:
            self.output_folder = Path(folder)
            self.output_label.config(text=f"{self.output_folder}")
            
            self.output_folder.mkdir(parents=True, exist_ok=True)
            
            messagebox.showinfo("Output Folder",
                                f"Output folder set to:\n{self.output_folder}")
    
    def open_export_folder(self, folder_path):
        import subprocess
        import sys
        import os
        
        folder_path = str(folder_path)
        
        if sys.platform == "win32":
            os.startfile(folder_path)
        elif sys.platform == "darwin":
            subprocess.run(["open", folder_path])
        else:
            subprocess.run(["xdg-open", folder_path])
    
    def export_selected_results(self):
        if not self.all_results:
            messagebox.showwarning("No data", "No analysis results to export.")
            return
        
        has_any_selected = False
        
        data_options = ['ap_parameter_matrix', 'raw_ap_data', 'frequency_drug_response',
                        'comprehensive_analysis', 'individual_traces', 'average_traces']
        
        for option in data_options:
            if self.export_settings[option].get():
                has_any_selected = True
                break
        
        figure_options = ['ap_overlay_raw', 'average_ap_sem', 'drug_comparison',
                          'frequency_comparison', 'stv_analysis', 'normalized_ap']
        
        for option in figure_options:
            if self.export_settings[option].get():
                has_any_selected = True
                break
        
        if not has_any_selected:
            messagebox.showwarning("No Export Options Selected",
                                   "Please select at least one export option.\n\n"
                                   "Go to 'Results Export' panel and check at least one option.")
            return
        
        export_name = self.export_name_var.get().strip()
        if not export_name:
            export_name = f"APEX_Export_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}"
            self.export_name_var.set(export_name)
        
        results_to_export = [res for res in self.all_results if not self.rejection_manager.is_rejected(res.get('trace_id', None))]
        
        #export_system = EnhancedExportSystem(self.output_folder, export_name)
        analysis_settings = {
            'species': self.selected_species.get(),
            'immature_mode': self.cardioid_immature_mode.get(),
            'smoothing_enabled': self.smoothing.get(),
            'smooth_method': self.smooth_method.get(),
            'smoothing_ms': self.smoothing_ms.get() if self.smoothing_ms.get() else 'adaptive',
            'dual_path': self.use_dual_path_detection.get(),
            'corrected_apd': self.use_corrected_apd.get()
        }
        export_system = EnhancedExportSystem(self.output_folder, export_name, analysis_settings)
        
        if hasattr(export_system, 'set_one_figure_per_cell'):
                export_system.set_one_figure_per_cell(self.export_settings['one_figure_per_cell'].get())
                
        export_options = {
            'ap_parameter_matrix': self.export_settings['ap_parameter_matrix'].get(),
            'raw_ap_data': self.export_settings['raw_ap_data'].get(),
            'frequency_drug_response': self.export_settings['frequency_drug_response'].get(),
            'comprehensive_analysis': self.export_settings['comprehensive_analysis'].get(),
            'individual_traces': self.export_settings['individual_traces'].get(),
            'average_traces': self.export_settings['average_traces'].get(),
            'figures': False,
            'figure_types': []
        }
        
        figure_keys = ['ap_overlay_raw', 'average_ap_sem', 'drug_comparison', 'frequency_comparison',
                       'stv_analysis', 'normalized_ap']
        
        selected_figures = []
        for fig_key in figure_keys:
            if self.export_settings[fig_key].get():
                selected_figures.append(fig_key)
        
        if selected_figures:
            export_options['figures'] = True
            export_options['figure_types'] = selected_figures
        
        try:
            export_folder = export_system.export_selected_results(
                results_to_export, export_options
            )
            
            if export_folder:
                exported_items = []
                
                if export_options['ap_parameter_matrix']:
                    exported_items.append("• AP Parameter Matrix (5 sheets)")
                if export_options['raw_ap_data']:
                    exported_items.append("• RAW AP Data Table")
                if export_options['frequency_drug_response']:
                    exported_items.append("• Frequency/Drug Response")
                if export_options['comprehensive_analysis']:
                    exported_items.append("• Comprehensive Analysis")
                if export_options['individual_traces']:
                    exported_items.append("• Individual Traces (CSV)")
                if export_options['average_traces']:
                    exported_items.append("• Average Traces (CSV)")
                
                if selected_figures:
                    exported_items.append(f"• {len(selected_figures)} Figure Types")
                
                summary_msg = f"Export completed!\n\n"
                summary_msg += f"Exported {len(results_to_export)} traces\n\n"
                summary_msg += "Exported items:\n" + "\n".join(exported_items)
                
                response = messagebox.askyesno("Export Complete",
                                               f"Results exported to:\n{export_folder}\n\n"
                                               f"{summary_msg}\n\n"
                                               "Do you want to open the export folder?")
                
                if response:
                    self.open_export_folder(export_folder)
        except Exception as e:
            messagebox.showerror("Export Error", f"Error during export:\n{str(e)}\n\n{traceback.format_exc()}")
            traceback.print_exc()
    
    def export_all_results(self):
        if not self.all_results:
            messagebox.showwarning("No data", "No analysis results to export.")
            return
        
        export_name = self.export_name_var.get().strip()
        if not export_name:
            export_name = f"APEX_All_Export_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}"
            self.export_name_var.set(export_name)
        
        #export_system = EnhancedExportSystem(self.output_folder, export_name)
        analysis_settings = {
            'species': self.selected_species.get(),
            'immature_mode': self.cardioid_immature_mode.get(),
            'smoothing_enabled': self.smoothing.get(),
            'smooth_method': self.smooth_method.get(),
            'smoothing_ms': self.smoothing_ms.get() if self.smoothing_ms.get() else 'adaptive',
            'dual_path': self.use_dual_path_detection.get(),
            'corrected_apd': self.use_corrected_apd.get()
        }
        export_system = EnhancedExportSystem(self.output_folder, export_name, analysis_settings)
        
        if hasattr(export_system, 'set_one_figure_per_cell'):
            export_system.set_one_figure_per_cell(self.export_settings['one_figure_per_cell'].get())
        
        export_options = {
            'figures': any([self.export_settings[fig].get() for fig in ['ap_overlay_raw', 'average_ap_sem',
                                                                        'drug_comparison', 'frequency_comparison',
                                                                        'stv_analysis', 'normalized_ap']]),
            'figure_types': []
        }
        
        figure_keys = ['ap_overlay_raw', 'average_ap_sem', 'drug_comparison', 'frequency_comparison',
                       'stv_analysis', 'normalized_ap']
        
        for fig_key in figure_keys:
            if self.export_settings[fig_key].get():
                export_options['figure_types'].append(fig_key)
        
        try:
            export_folder = export_system.export_selected_results(
                self.all_results, export_options
            )
            
            if export_folder:
                response = messagebox.askyesno("Export Complete",
                                               f"All results exported to:\n{export_folder}\n\n"
                                               "Do you want to open the export folder?")
                
                if response:
                    self.open_export_folder(export_folder)
        except Exception as e:
            messagebox.showerror("Export Error", f"Error during export:\n{str(e)}")
            traceback.print_exc()
    
    def export_stacked_files_only(self):
        if not self.stacked_files:
            messagebox.showwarning("No Stacked Files", "No stacked files available to export.")
            return
        
        export_name = self.export_name_var.get().strip()
        if not export_name:
            export_name = f"APEX_Stacked_Export_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}"
            self.export_name_var.set(export_name)
        
        file_path = filedialog.asksaveasfilename(
            title="Save Stacked Excel File",
            defaultextension=".xlsx",
            filetypes=[("Excel files", "*.xlsx"), ("All files", "*.*")]
        )
        
        if not file_path:
            return
        
        try:
            with pd.ExcelWriter(file_path, engine='openpyxl') as writer:
                for group_name, data in self.stacked_files.items():
                    time = data['time']
                    
                    df_dict = {'Time_ms': time}
                    for i, trace in enumerate(data['traces']):
                        df_dict[f'Trace_{i + 1}'] = trace['data'][:len(time)]
                    
                    df = pd.DataFrame(df_dict)
                    # Sanitize sheet name for Excel
                    safe_sheet_name = sanitize_excel_sheet_name(group_name, 31)
                    df.to_excel(writer, sheet_name=safe_sheet_name, index=False)
                
                metadata = []
                for group_name, data in self.stacked_files.items():
                    for i, trace in enumerate(data['traces']):
                        trace_file = trace.get('file', '')
                        trace_meta = {}
                        
                        for file_path_key, meta in self.file_metadata.items():
                            if Path(file_path_key).name == trace_file:
                                trace_meta = meta
                                break
                        
                        metadata.append({
                            'Group': group_name,
                            'Trace': f'Trace_{i + 1}',
                            'Original_File': trace_file,
                            'Cell_ID': trace_meta.get('cell_id', trace.get('cell_id', 'Unknown')),
                            'Frequency_Hz': trace_meta.get('frequency', trace.get('frequency', 'Unknown')),
                            'Drug': trace_meta.get('drug', trace.get('drug', 'None')),
                            'Concentration': trace_meta.get('concentration', trace.get('concentration', '')),
                            'Condition': trace.get('condition', '')
                        })
                
                if metadata:
                    pd.DataFrame(metadata).to_excel(writer, sheet_name='Metadata', index=False)
            
            messagebox.showinfo("Export Complete", f"Stacked files exported to:\n{file_path}")
            
        except Exception as e:
            messagebox.showerror("Export Error", f"Could not export stacked files: {str(e)}")
            traceback.print_exc()
    
    def reanalyze_all_traces(self):
        """Reanalyze all traces from scratch"""
        response = messagebox.askyesno("Reanalyze All",
                                       "This will clear all existing analysis results and reanalyze all files.\n\n"
                                       "Corrections (peak, upstroke, late repol) will be preserved.\n\n"
                                       "Do you want to continue?")
        if not response:
            return
        
        # Clear analyzed trace IDs and results
        self.analyzed_trace_ids.clear()
        self.all_results.clear()
        self.validated_traces.clear()
        
        # Rerun analysis
        self.run_professional_analysis()
    
    def run_professional_analysis(self):
        """Run professional analysis with incremental processing (preserve existing results)"""
        if not self.file_list and not self.stacked_files:
            messagebox.showwarning("No files", "Please add files to analyze.")
            return
        
        # Store current results and analyze only new files
        existing_results = self.all_results.copy()
        existing_trace_ids = set(self.analyzed_trace_ids)
        
        # Clear results but keep corrections
        self.all_results = []
        self.progress['value'] = 0
        
        total_items = len(self.file_list) + len(self.stacked_files)
        if total_items == 0:
            return
        
        self.progress['maximum'] = total_items
        current_item = 0
        
        new_analysis_needed = False
        
        if self.file_list:
            for fpath in self.file_list:
                # Check if this file was already analyzed
                trace_id = (fpath, 0)  # Simple check for single file
                if trace_id not in existing_trace_ids:
                    self.process_single_file(fpath)
                    new_analysis_needed = True
                else:
                    # Find and preserve existing result
                    for res in existing_results:
                        if res.get('trace_id') == trace_id:
                            self.all_results.append(res)
                            break
                
                current_item += 1
                self.progress['value'] = current_item
                self.root.update_idletasks()
        
        if self.stacked_files:
            for cell_id, stacked_data in self.stacked_files.items():
                # Check if stacked traces were analyzed
                stacked_needed = False
                for i, trace_info in enumerate(stacked_data.get('traces', [])):
                    trace_id = (f"Stacked_{cell_id}", i)
                    if trace_id not in existing_trace_ids:
                        stacked_needed = True
                        break
                
                if stacked_needed:
                    self.process_stacked_file(cell_id, stacked_data)
                    new_analysis_needed = True
                else:
                    # Preserve existing results for this stacked file
                    for res in existing_results:
                        if res.get('cell_id') == cell_id and res.get('file_type') == 'Stacked':
                            self.all_results.append(res)
                
                current_item += 1
                self.progress['value'] = current_item
                self.root.update_idletasks()
        
        # Update analyzed trace IDs
        for res in self.all_results:
            trace_id = res.get('trace_id')
            if trace_id:
                self.analyzed_trace_ids.add(trace_id)
        
        self.current_trace_index = 0
        if self.all_results:
            self.plot_current_trace()
        
        self.update_results_table()
        
        total_traces = len(self.all_results)
        total_aps = sum(len(res.get('ap_metrics', [])) for res in self.all_results)
        
        adaptive_used = sum(1 for res in self.all_results if res.get('adaptive_smoothing_used', False))
        immature_used = sum(1 for res in self.all_results if res.get('immature_mode_used', False))
        
        if new_analysis_needed:
            msg = f"APEX professional analysis finished!\n\n"
            msg += f"• Total traces analyzed: {total_traces}\n"
            msg += f"• Valid APs detected: {total_aps}\n"
            msg += f"• RMP measured from baseline (first 10 ms)\n"
            msg += f"• ENHANCED: Upstroke dV/dt calculated with minimal smoothing (0.5ms)\n"
            msg += f"• Adaptive smoothing used: {adaptive_used} traces\n"
            if immature_used > 0:
                msg += f"• Cardioid Immature Mode used: {immature_used} traces\n"
            msg += f"• Dual-path peak detection: {'Enabled' if self.use_dual_path_detection.get() else 'Disabled'}\n"
            msg += f"• Corrected APD80/90: {'Enabled' if self.use_corrected_apd.get() else 'Disabled'}\n"
            msg += f"• Species-specific validation: Enabled\n"
            msg += f"• Repolarization Fraction: Calculated\n\n"
            msg += f"Ready for validation and export."
            
            messagebox.showinfo("Professional Analysis Complete", msg)
    
    def process_single_file(self, fpath):
        try:
            parsed_meta = self.parsed_files.get(fpath)
            file_meta = self.file_metadata.get(fpath, {})
            
            species = file_meta.get('species', 'default')
            if self.selected_species.get() != 'auto':
                species = self.selected_species.get()
            
            file_type = 'ABF' if fpath.endswith('.abf') else 'CSV/Excel'
            
            if fpath.endswith('.abf'):
                selected_ranges = self.abf_trace_selections.get(fpath)
                sweeps = read_abf_file(fpath, selected_ranges)
                
                for sweep in sweeps:
                    trace_id = (fpath, sweep['sweep_number'])
                    
                    if self.rejection_manager.is_rejected(trace_id):
                        continue
                    
                    time = sweep['time']
                    voltage = sweep['voltage']
                    
                    if len(time) < 10:
                        continue
                    
                    corrected_peak_idx = None
                    corrected_upstroke_idx = None
                    
                    if trace_id in self.manual_peak_corrections and 0 in self.manual_peak_corrections[trace_id]:
                        corrected_peak_idx = self.manual_peak_corrections[trace_id][0]
                    
                    if trace_id in self.manual_upstroke_corrections and 0 in self.manual_upstroke_corrections[trace_id]:
                        corrected_upstroke_idx = self.manual_upstroke_corrections[trace_id][0]
                    
                    # Get immature mode status
                    immature_mode = self.cardioid_immature_mode.get() and species == 'cardioid'
                    
                    if corrected_peak_idx is not None:
                        result = self.analyze_trace_with_corrected_peak(time, voltage, corrected_peak_idx, species,
                                                                        corrected_upstroke_idx)
                    else:
                        smoothing_ms_val = self.get_smoothing_ms_value()
                        result = analyze_trace_enhanced_dualpath_v3(
                            time, voltage, species,
                            smoothing=self.smoothing.get(),
                            smooth_method=self.smooth_method.get(),
                            smoothing_ms=smoothing_ms_val,
                            min_apd90=float(self.min_apd90.get()),
                            use_biological_peak_detection=self.use_biological_detection.get(),
                            use_corrected_apd=self.use_corrected_apd.get(),
                            file_type=file_type,
                            immature_mode=immature_mode
                        )
                        
                        if corrected_upstroke_idx is not None and result.get('ap_metrics'):
                            for ap in result['ap_metrics']:
                                ap['has_manual_upstroke'] = True
                                current_type = ap.get('correction_type', 'auto')
                                if current_type == 'auto':
                                    ap['correction_type'] = 'manual_upstroke'
                                elif 'manual_upstroke' not in current_type:
                                    ap['correction_type'] = f'{current_type}+manual_upstroke'
                    
                    if trace_id in self.late_repolarization_corrections:
                        for ap_idx, corrected in self.late_repolarization_corrections[trace_id].items():
                            if corrected and ap_idx < len(result['ap_metrics']):
                                ap = result['ap_metrics'][ap_idx]
                                rmp = ap.get('RMP', np.nan)
                                peak_v = result['voltage_smooth'][ap['peak_idx']] if ap['peak_idx'] < len(result['voltage_smooth']) else np.nan
                                apply_late_repolarization_correction_to_metrics(result['time'], result['voltage_smooth'],
                                                               ap, ap['peak_idx'], rmp, peak_v)
                                ap['has_late_repol'] = True
                                current_type = ap.get('correction_type', 'auto')
                                if current_type == 'auto':
                                    ap['correction_type'] = 'late_repol'
                                elif 'late_repol' not in current_type:
                                    ap['correction_type'] = f'{current_type}+late_repol'
                    
                    self.add_result_metadata(result, fpath, file_meta, sweep)
                    self.all_results.append(result)
                    
            else:
                trace_id = (fpath, 0)
                
                if self.rejection_manager.is_rejected(trace_id):
                    return
                
                try:
                    # Try PatchMaster parser first
                    time_arr, volt_arr, pm_meta = parse_patchmaster_csv(fpath)
                    if time_arr is not None and volt_arr is not None:
                        time = time_arr
                        voltage = volt_arr
                    else:
                        if fpath.endswith('.csv'):
                            df = pd.read_csv(fpath)
                        else:
                            df = pd.read_excel(fpath)
                        
                        tcol, vcol = fuzzy_find_columns(df)
                        if tcol is None or vcol is None:
                            return
                        
                        time = np.array(df[tcol].astype(float).values)
                        voltage = np.array(df[vcol].astype(float).values)
                except Exception as e:
                    print(f"Error reading file {fpath}: {e}")
                    return
                
                if len(time) < 10:
                    return
                
                corrected_peak_idx = None
                corrected_upstroke_idx = None
                
                if trace_id in self.manual_peak_corrections and 0 in self.manual_peak_corrections[trace_id]:
                    corrected_peak_idx = self.manual_peak_corrections[trace_id][0]
                
                if trace_id in self.manual_upstroke_corrections and 0 in self.manual_upstroke_corrections[trace_id]:
                    corrected_upstroke_idx = self.manual_upstroke_corrections[trace_id][0]
                
                # Get immature mode status
                immature_mode = self.cardioid_immature_mode.get() and species == 'cardioid'
                
                if corrected_peak_idx is not None:
                    result = self.analyze_trace_with_corrected_peak(time, voltage, corrected_peak_idx, species,
                                                                    corrected_upstroke_idx)
                else:
                    smoothing_ms_val = self.get_smoothing_ms_value()
                    result = analyze_trace_enhanced_dualpath_v3(
                        time, voltage, species,
                        smoothing=self.smoothing.get(),
                        smooth_method=self.smooth_method.get(),
                        smoothing_ms=smoothing_ms_val,
                        min_apd90=float(self.min_apd90.get()),
                        use_biological_peak_detection=self.use_biological_detection.get(),
                        use_corrected_apd=self.use_corrected_apd.get(),
                        file_type=file_type,
                        immature_mode=immature_mode
                    )
                    
                    if corrected_upstroke_idx is not None and result.get('ap_metrics'):
                        for ap in result['ap_metrics']:
                            ap['has_manual_upstroke'] = True
                            current_type = ap.get('correction_type', 'auto')
                            if current_type == 'auto':
                                ap['correction_type'] = 'manual_upstroke'
                            elif 'manual_upstroke' not in current_type:
                                ap['correction_type'] = f'{current_type}+manual_upstroke'
                
                if trace_id in self.late_repolarization_corrections:
                    for ap_idx, corrected in self.late_repolarization_corrections[trace_id].items():
                        if corrected and ap_idx < len(result['ap_metrics']):
                            ap = result['ap_metrics'][ap_idx]
                            rmp = ap.get('RMP', np.nan)
                            peak_v = result['voltage_smooth'][ap['peak_idx']] if ap['peak_idx'] < len(result['voltage_smooth']) else np.nan
                            apply_late_repolarization_correction_to_metrics(result['time'], result['voltage_smooth'],
                                                           ap, ap['peak_idx'], rmp, peak_v)
                            ap['has_late_repol'] = True
                            current_type = ap.get('correction_type', 'auto')
                            if current_type == 'auto':
                                ap['correction_type'] = 'late_repol'
                            elif 'late_repol' not in current_type:
                                ap['correction_type'] = f'{current_type}+late_repol'
                
                self.add_result_metadata(result, fpath, file_meta)
                self.all_results.append(result)
                
        except Exception as e:
            print(f"Error processing file {fpath}: {e}")
            traceback.print_exc()
    
    def analyze_trace_with_corrected_peak(self, time, voltage, corrected_peak_idx, species='default',
                                        corrected_upstroke_idx=None):
        dt_ms = float(time[1] - time[0]) if len(time) > 1 else 0.1
        smoothing_ms = self.get_smoothing_ms_value()
        if smoothing_ms is None or smoothing_ms <= 0:
            smoothing_ms = calculate_adaptive_smoothing(dt_ms, species, 'CSV/Excel')
    
        # Create the fully smoothed trace for visualization
        v_smooth = smooth_voltage(voltage, method=self.smooth_method.get(),
                                  window_ms=smoothing_ms, dt_ms=dt_ms) if self.smoothing.get() else voltage
    
        # CRITICAL: Create minimally-smoothed trace for accurate upstroke detection
        minimal_smoothing_ms = 0.1
        v_minimal_smooth = smooth_voltage(voltage, method='savgol',
                                          window_ms=minimal_smoothing_ms, dt_ms=dt_ms) if dt_ms > 0 else voltage
    
        detection = {
            'stim_times_idx': np.array([], dtype=int),
            'stim_times_ms': [],
            'all_candidate_peaks_idx': np.array([], dtype=int),
            'real_ap_peaks_idx': np.array([corrected_peak_idx], dtype=int)
        }
    
        # Get immature mode status
        immature_mode = self.cardioid_immature_mode.get() and species == 'cardioid'

        ap_metrics = []
        try:
            # Use v_minimal_smooth for accurate upstroke detection
            m = compute_apd_metrics_enhanced_v3(time, v_minimal_smooth, corrected_peak_idx, species=species,
                                               use_corrected_apd=self.use_corrected_apd.get(),
                                               manual_upstroke_idx=corrected_upstroke_idx,
                                               immature_mode=immature_mode)
            m['has_manual_correction'] = True
            if corrected_upstroke_idx is not None:
                m['has_manual_upstroke'] = True
                m['correction_type'] = 'manual_peak+manual_upstroke'
            else:
                m['correction_type'] = 'manual_peak'
            if species == 'cardioid':
                is_valid, reason = is_cardioid_ap(m, species, immature_mode)
            else:
                is_valid, reason = is_physiologically_valid_ap(m, species, immature_mode=immature_mode)
            if is_valid:
                ap_metrics.append(m)
            else:
                print(f"Rejected AP with corrected peak: {reason}")
        except Exception as e:
            print(f"Error computing metrics: {e}")
    
        apd90_values = [m.get('APD90', np.nan) for m in ap_metrics if not math.isnan(m.get('APD90', np.nan))]
        stv_apd90, stv_note = calculate_stv(apd90_values)
    
        return {
            'time': np.array(time),
            'voltage_raw': np.array(voltage),
            'voltage_smooth': np.array(v_smooth),
            'voltage_minimal_smooth': np.array(v_minimal_smooth),
            'dt_ms': dt_ms,
            'detection': detection,
            'ap_metrics': ap_metrics,
            'stv_apd90': stv_apd90,
            'stv_note': stv_note,
            'has_manual_correction': True,
            'has_upstroke_correction': corrected_upstroke_idx is not None,
            'use_corrected_apd': self.use_corrected_apd.get(),
            'adaptive_smoothing_used': self.get_smoothing_ms_value() is None or self.get_smoothing_ms_value() <= 0,
            'smoothing_ms_used': smoothing_ms,
            'sampling_rate_hz': 1000.0 / dt_ms if dt_ms > 0 else 1000,
            'immature_mode_used': immature_mode
        }
    
    def process_stacked_file(self, cell_id, stacked_data):
        """Process a stacked file with proper analysis matching single traces"""
        try:
            time = stacked_data['time']
            traces = stacked_data['traces']
            
            # Group traces by frequency to ensure consistent analysis
            freq_groups = defaultdict(list)
            for i, trace_info in enumerate(traces):
                freq = trace_info.get('frequency', '1.0')
                freq_groups[freq].append((i, trace_info))
            
            for freq, trace_list in freq_groups.items():
                for i, trace_info in trace_list:
                    trace_id = (f"Stacked_{cell_id}", i)
                    
                    if self.rejection_manager.is_rejected(trace_id):
                        continue
                    
                    voltage = trace_info['data']
                    
                    # Ensure time and voltage are same length
                    if len(time) != len(voltage):
                        min_len = min(len(time), len(voltage))
                        time_trimmed = time[:min_len]
                        voltage_trimmed = voltage[:min_len]
                    else:
                        time_trimmed = time
                        voltage_trimmed = voltage
                    
                    if len(time_trimmed) < 10:
                        continue
                    
                    # Use species from metadata or auto-detect
                    species = 'default'
                    if cell_id in self.file_metadata:
                        species = self.file_metadata.get(cell_id, {}).get('species', 'default')
                    
                    # IMPORTANT: Use the SAME analysis parameters as single traces
                    smoothing_ms_val = self.get_smoothing_ms_value()
                    
                    # Check if smoothing is disabled
                    smoothing_enabled = self.smoothing.get()
                    if smoothing_ms_val is not None and smoothing_ms_val <= 0:
                        smoothing_enabled = False
                    
                    # Get immature mode status
                    immature_mode = self.cardioid_immature_mode.get() and species == 'cardioid'
                    
                    result = analyze_trace_enhanced_dualpath_v3(
                        time_trimmed, voltage_trimmed, species,
                        smoothing=smoothing_enabled,
                        smooth_method=self.smooth_method.get(),
                        smoothing_ms=smoothing_ms_val,
                        min_apd90=float(self.min_apd90.get()),
                        use_biological_peak_detection=self.use_biological_detection.get(),
                        use_corrected_apd=self.use_corrected_apd.get(),
                        file_type='CSV/Excel',
                        immature_mode=immature_mode
                    )
                    
                    result['file'] = f"Stacked_{cell_id}"
                    result['file_name'] = f"{cell_id}_trace{i + 1}"
                    result['cell_id'] = cell_id
                    result['display_cell_id'] = cell_id
                    result['frequency'] = trace_info.get('frequency', freq)
                    result['file_type'] = 'Stacked'
                    result['sweep_number'] = i
                    result['total_sweeps'] = len(traces)
                    result['trace_id'] = trace_id
                    result['species'] = species
                    result['drug'] = trace_info.get('drug', 'None')
                    result['concentration'] = trace_info.get('concentration', '')
                    result['range_name'] = f"Stacked_Trace_{i + 1}"
                    
                    self.all_results.append(result)
                    
        except Exception as e:
            print(f"Error processing stacked file {cell_id}: {e}")
            traceback.print_exc()
    
    def add_result_metadata(self, result, fpath, file_meta, sweep=None):
        if sweep:
            file_name = f"{Path(fpath).stem}_trace{sweep['sweep_number'] + 1}"
        else:
            file_name = Path(fpath).name
        
        result['file'] = fpath
        result['file_name'] = file_name
        result['cell_id'] = file_meta.get('cell_id', 'unknown')
        result['display_cell_id'] = file_meta.get('display_cell_id', file_meta.get('cell_id', 'unknown'))
        result['frequency'] = file_meta.get('frequency', 'unknown')
        result['file_type'] = 'ABF' if fpath.endswith('.abf') else 'CSV/Excel'
        result['sweep_number'] = sweep['sweep_number'] if sweep else 0
        result['total_sweeps'] = 1 if not sweep else 'multiple'
        result['trace_id'] = (fpath, sweep['sweep_number'] if sweep else 0)
        result['species'] = file_meta.get('species', 'default')
        
        if fpath.endswith('.xlsx') or fpath.endswith('.csv'):
            result['range_name'] = file_name
            
            import re
            match = re.search(r'_(\d+)\.(?:xlsx|csv)$', file_name)
            if match:
                result['sweep_number_from_filename'] = int(match.group(1))
            else:
                result['sweep_number_from_filename'] = 0
        elif sweep:
            result['drug'] = sweep.get('drug', file_meta.get('drug', 'None'))
            result['concentration'] = sweep.get('concentration', file_meta.get('concentration', ''))
            result['range_name'] = sweep.get('range_name', file_meta.get('range_name', ''))
            result['range_description'] = sweep.get('range_description', '')
        else:
            result['drug'] = file_meta.get('drug', 'None')
            result['concentration'] = file_meta.get('concentration', '')
            result['range_name'] = file_meta.get('range_name', '')


# ============================================================================
# Selective Batch Correction Dialog
# ============================================================================

class SelectiveBatchCorrectionDialog(tk.Toplevel):
    """Dialog for batch correction with individual AP selection and intelligent pre-selection"""
    
    def __init__(self, parent, correction_type, current_ap, similar_aps, 
                 current_trace_info, get_ap_info_callback):
        super().__init__(parent)
        self.parent = parent
        self.correction_type = correction_type
        self.current_ap = current_ap
        self.similar_aps = similar_aps
        self.current_trace_info = current_trace_info
        self.get_ap_info_callback = get_ap_info_callback
        self.selected_pairs = []
        
        # Set title based on correction type
        type_title = correction_type.title().replace('_', ' ')
        self.title(f"Apply {type_title} Correction to Similar APs")
        self.geometry("800x650")
        self.transient(parent)
        self.grab_set()
        
        self.configure(bg='white')
        
        # Main container
        main_container = ttk.Frame(self)
        main_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Header
        header_frame = ttk.Frame(main_container)
        header_frame.pack(fill=tk.X, pady=(0, 10))
        
        header = ttk.Label(header_frame, text=f"Apply {type_title} Correction",
                           font=("Helvetica", 14, "bold"), background='white')
        header.pack()
        
        # Current AP preview
        preview_frame = ttk.LabelFrame(main_container, text="Current AP (Already Corrected)", padding=10)
        preview_frame.pack(fill=tk.X, pady=(0, 10))
        
        apa = current_ap.get('APA', 0)
        apd90 = current_ap.get('APD90', 0)
        dvdt = current_ap.get('dVdt_max', 0)
        rmp = current_ap.get('RMP', 0)
        correction_type_display = current_ap.get('correction_type', 'auto').replace('_', ' ').title()
        
        features_text = (
            f"📁 File: {current_trace_info.get('file_name', 'unknown')}\n"
            f"🔬 Cell: {current_trace_info.get('cell_id', 'unknown')} | "
            f"⚡ Frequency: {current_trace_info.get('frequency', 'unknown')} Hz\n"
            f"📊 APA: {apa:.1f} mV | APD90: {apd90:.1f} ms | dV/dt: {dvdt:.1f} mV/ms | RMP: {rmp:.1f} mV\n"
            f"🔄 Correction Type: {correction_type_display}"
        )
        
        info_label = tk.Label(preview_frame, text=features_text, justify=tk.LEFT, 
                              background='white', font=("Helvetica", 9))
        info_label.pack(anchor='w', padx=5, pady=5)
        
        # Similar APs selection frame
        selection_frame = ttk.LabelFrame(main_container, text="Select Similar APs to Apply Correction", padding=10)
        selection_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # Control buttons for selection
        control_frame = ttk.Frame(selection_frame)
        control_frame.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Button(control_frame, text="Select All", 
                  command=self.select_all, width=12).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Select None", 
                  command=self.select_none, width=12).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Select High Similarity (>95%)", 
                  command=self.select_high_similarity, width=20).pack(side=tk.LEFT, padx=5)
        
        # Status label
        self.status_label = ttk.Label(control_frame, text="", font=("Helvetica", 9))
        self.status_label.pack(side=tk.RIGHT, padx=10)
        
        # Create canvas with scrollbar for scrollable AP list
        canvas_frame = ttk.Frame(selection_frame)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        
        canvas = tk.Canvas(canvas_frame, highlightthickness=0, bg='white')
        scrollbar = ttk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=canvas.yview)
        self.scrollable_frame = ttk.Frame(canvas)
        
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Store checkbox variables for each AP
        self.check_vars = []
        self.ap_frames = []
        
        # Populate the list of similar APs with checkboxes and intelligent pre-selection
        if similar_aps:
            # Show similarity range summary
            similarities = [sim for _, _, sim in similar_aps]
            min_sim = min(similarities) * 100
            max_sim = max(similarities) * 100
            avg_sim = np.mean(similarities) * 100
            
            summary_label = tk.Label(self.scrollable_frame,
                                     text=f"Found {len(similar_aps)} APs with similar morphology\n"
                                          f"Similarity range: {min_sim:.0f}% - {max_sim:.0f}% (avg: {avg_sim:.0f}%)\n"
                                          f"• APs with >95% similarity will be automatically selected",
                                     font=("Helvetica", 10, "bold"),
                                     bg='#E8F4FD', fg='#0066CC',
                                     pady=5)
            summary_label.pack(fill=tk.X, pady=(0, 10))
            
            # Add separator
            ttk.Separator(self.scrollable_frame, orient='horizontal').pack(fill=tk.X, pady=5)
            
            # Show each similar AP with checkbox and intelligent pre-selection
            for i, (trace_idx, ap_idx, similarity) in enumerate(similar_aps):
                ap_info = self.get_ap_info_callback(trace_idx, ap_idx)
                
                if ap_info:
                    # Create frame for this AP
                    ap_frame = ttk.Frame(self.scrollable_frame)
                    ap_frame.pack(fill=tk.X, pady=5, padx=5)
                    self.ap_frames.append(ap_frame)
                    
                    # Create checkbox variable with intelligent pre-selection
                    sim_percent = float(similarity) * 100
                    default_selected = sim_percent > 95
                    
                    var = tk.BooleanVar(value=bool(default_selected))
                    self.check_vars.append(var)
                    
                    # Checkbox
                    cb = tk.Checkbutton(ap_frame, variable=var,
                                       bg='white', activebackground='white',
                                       command=lambda idx=i: self.update_status())
                    cb.pack(side=tk.LEFT, padx=(0, 10))
                    
                    # Create frame for AP details
                    details_frame = ttk.Frame(ap_frame)
                    details_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
                    
                    # Similarity with color coding (adjusted thresholds for 95% auto-selection)
                    if sim_percent >= 95:
                        sim_color = "green"
                        sim_bg = "#E8F5E9"
                        sim_text = f"Similarity: {sim_percent:.0f}% ★ (Excellent - Auto-selected)"
                    elif sim_percent >= 85:
                        sim_color = "blue"
                        sim_bg = "#E3F2FD"
                        sim_text = f"Similarity: {sim_percent:.0f}% (High)"
                    elif sim_percent >= 70:
                        sim_color = "orange"
                        sim_bg = "#FFF3E0"
                        sim_text = f"Similarity: {sim_percent:.0f}% (Medium)"
                    else:
                        sim_color = "red"
                        sim_bg = "#FFEBEE"
                        sim_text = f"Similarity: {sim_percent:.0f}% (Low)"
                    
                    # Header with file info and similarity
                    header_frame = tk.Frame(details_frame, bg=sim_bg, relief=tk.GROOVE, bd=1)
                    header_frame.pack(fill=tk.X, pady=(0, 5))
                    
                    similarity_label = tk.Label(header_frame, text=sim_text,
                                                fg=sim_color, font=("Helvetica", 9, "bold"),
                                                bg=sim_bg, padx=5, pady=2)
                    similarity_label.pack(side=tk.RIGHT, padx=5)
                    
                    file_info = f"📄 {ap_info['trace_name'][:50]}"
                    file_label = tk.Label(header_frame, text=file_info,
                                          font=("Helvetica", 9),
                                          bg=sim_bg, padx=5, pady=2)
                    file_label.pack(side=tk.LEFT)
                    
                    # Metrics frame
                    metrics_frame = ttk.Frame(details_frame)
                    metrics_frame.pack(fill=tk.X, pady=2)
                    
                    # Key metrics in a grid
                    metrics = [
                        ("Cell", ap_info.get('cell_id', 'N/A')),
                        ("Freq", f"{ap_info.get('frequency', 'N/A')} Hz"),
                        ("Drug", ap_info.get('drug', 'None')),
                        ("APA", f"{ap_info.get('apa', 0):.1f} mV"),
                        ("APD90", f"{ap_info.get('apd90', 0):.1f} ms"),
                        ("dV/dt", f"{ap_info.get('dvdt', 0):.1f} mV/ms"),
                        ("RMP", f"{ap_info.get('rmp', 0):.1f} mV")
                    ]
                    
                    for j, (label, value) in enumerate(metrics):
                        row = j // 4
                        col = j % 4
                        
                        metric_frame = ttk.Frame(metrics_frame)
                        metric_frame.grid(row=row, column=col, sticky='w', padx=10, pady=2)
                        
                        ttk.Label(metric_frame, text=f"{label}:", font=("Helvetica", 8, "bold")).pack(side=tk.LEFT)
                        ttk.Label(metric_frame, text=value, font=("Helvetica", 8)).pack(side=tk.LEFT, padx=(5, 0))
                    
                    # Add separator line between APs
                    if i < len(similar_aps) - 1:
                        ttk.Separator(self.scrollable_frame, orient='horizontal').pack(fill=tk.X, pady=5)
        else:
            # No similar APs found
            no_aps_label = tk.Label(self.scrollable_frame,
                                   text="No similar APs found.\n\nTry lowering the similarity threshold or check if there are other APs loaded.",
                                   font=("Helvetica", 10),
                                   fg="gray", bg='white', justify=tk.CENTER)
            no_aps_label.pack(expand=True, pady=50)
        
        # Buttons frame
        button_frame = ttk.Frame(main_container)
        button_frame.pack(fill=tk.X, pady=10)
        
        # Show selected count
        self.selected_count_label = ttk.Label(button_frame, text="", font=("Helvetica", 10))
        self.selected_count_label.pack(side=tk.LEFT, padx=10)
        
        ttk.Button(button_frame, text=f"Apply to Selected APs", 
                  command=self.apply_selected, width=20).pack(side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="Cancel", 
                  command=self.cancel, width=15).pack(side=tk.RIGHT, padx=5)
        
        # Initial status update
        self.update_status()
    
    def update_status(self):
        """Update status label with selected count"""
        selected_count = sum(1 for var in self.check_vars if var.get())
        total_count = len(self.check_vars)
        self.status_label.config(text=f"Selected: {selected_count} / {total_count} APs")
        self.selected_count_label.config(text=f"Selected: {selected_count} APs")
    
    def select_all(self):
        """Select all APs"""
        for var in self.check_vars:
            var.set(True)
        self.update_status()
    
    def select_none(self):
        """Deselect all APs"""
        for var in self.check_vars:
            var.set(False)
        self.update_status()
    
    def select_high_similarity(self):
        """Select APs with similarity > 95%"""
        for i, (_, _, similarity) in enumerate(self.similar_aps):
            if similarity >= 0.95:
                self.check_vars[i].set(True)
            else:
                self.check_vars[i].set(False)
        self.update_status()
    
    def apply_selected(self):
        """Apply correction to selected APs"""
        self.selected_pairs = []
        for i, (trace_idx, ap_idx, _) in enumerate(self.similar_aps):
            if i < len(self.check_vars) and self.check_vars[i].get():
                self.selected_pairs.append((trace_idx, ap_idx))
        
        self.destroy()
    
    def cancel(self):
        """Cancel and close dialog"""
        self.selected_pairs = []
        self.destroy()
    
    def get_selected_pairs(self):
        """Return list of selected (trace_idx, ap_idx) pairs"""
        return self.selected_pairs


# ============================================================================
# Batch Progress Dialog
# ============================================================================

class BatchProgressDialog:
    """Progress dialog for batch operations"""
    
    def __init__(self, parent, title="Applying Corrections", total=100):
        self.parent = parent
        self.total = total
        self.cancelled = False
        self.completed = 0
        
        self.dialog = tk.Toplevel(parent)
        self.dialog.title(title)
        self.dialog.geometry("450x150")
        self.dialog.transient(parent)
        self.dialog.grab_set()
        
        self.dialog.configure(bg='white')
        
        # Center on parent
        self.dialog.update_idletasks()
        x = parent.winfo_x() + (parent.winfo_width() // 2) - (450 // 2)
        y = parent.winfo_y() + (parent.winfo_height() // 2) - (150 // 2)
        self.dialog.geometry(f"+{x}+{y}")
        
        # Progress bar
        ttk.Label(self.dialog, text=title, font=("Helvetica", 11, "bold"),
                 background='white').pack(pady=10)
        
        self.status_label = ttk.Label(self.dialog, text="Starting...", background='white')
        self.status_label.pack(pady=5)
        
        self.progress_bar = ttk.Progressbar(self.dialog, mode='determinate', 
                                           maximum=total, length=400)
        self.progress_bar.pack(pady=10, padx=20)
        
        self.cancel_btn = ttk.Button(self.dialog, text="Cancel", command=self.cancel)
        self.cancel_btn.pack(pady=10)
        
        self.dialog.protocol("WM_DELETE_WINDOW", self.cancel)
    
    def update(self, current, status_text=None):
        """Update progress"""
        self.completed = current
        self.progress_bar['value'] = current
        if status_text:
            self.status_label.config(text=status_text)
        self.dialog.update_idletasks()
    
    def is_cancelled(self):
        """Check if operation was cancelled"""
        return self.cancelled
    
    def cancel(self):
        """Cancel operation"""
        self.cancelled = True
        self.dialog.destroy()
    
    def close(self):
        """Close dialog"""
        self.dialog.destroy()


# ============================================================================
# Correction Management Functions
# ============================================================================

def calculate_similarity_score(current_ap, candidate_ap):
    """Calculate similarity score based on APD90, APA, and dV/dt_max"""
    current_apd90 = current_ap.get('APD90', np.nan)
    current_apa = current_ap.get('APA', np.nan)
    current_dvdt = current_ap.get('dVdt_max', np.nan)
    
    candidate_apd90 = candidate_ap.get('APD90', np.nan)
    candidate_apa = candidate_ap.get('APA', np.nan)
    candidate_dvdt = candidate_ap.get('dVdt_max', np.nan)
    
    scores = []
    
    # APD90 similarity (40% weight)
    if not math.isnan(current_apd90) and not math.isnan(candidate_apd90) and current_apd90 > 0:
        ratio = min(current_apd90, candidate_apd90) / max(current_apd90, candidate_apd90)
        scores.append(ratio * 0.4)
    
    # APA similarity (30% weight)
    if not math.isnan(current_apa) and not math.isnan(candidate_apa) and current_apa > 0:
        ratio = min(current_apa, candidate_apa) / max(current_apa, candidate_apa)
        scores.append(ratio * 0.3)
    
    # dV/dt_max similarity (30% weight)
    if not math.isnan(current_dvdt) and not math.isnan(candidate_dvdt) and current_dvdt > 0:
        ratio = min(current_dvdt, candidate_dvdt) / max(current_dvdt, candidate_dvdt)
        scores.append(ratio * 0.3)
    
    if scores:
        return sum(scores)
    else:
        return 0.5


# ============================================================================
# Main Application Entry Point
# ============================================================================

def calculate_rmp_from_baseline(time, voltage, baseline_window_ms=10):
    """Calculate RMP from the first X ms of the trace only."""
    dt = time[1] - time[0] if len(time) > 1 else 0.1
    n_samples = int(baseline_window_ms / dt)
    
    if n_samples > len(voltage):
        n_samples = min(len(voltage), 50)
    
    rmp = np.median(voltage[:n_samples])
    
    return rmp, f"Baseline ({baseline_window_ms} ms window)"


def parse_patchmaster_csv(file_path):
    """Parse PatchMaster/HEKA CSV files"""
    try:
        # Try to read with pandas, auto-detect header
        df = pd.read_csv(file_path)
        
        # Look for time and voltage columns
        time_col = None
        voltage_col = None
        
        # PatchMaster specific column names
        for col in df.columns:
            col_lower = col.lower().strip()
            if 'time' in col_lower or col_lower == 't':
                time_col = col
            elif 'vmon' in col_lower or 'vm' in col_lower or 'voltage' in col_lower or col_lower == 'v':
                voltage_col = col
        
        # If not found, use fuzzy matching
        if time_col is None or voltage_col is None:
            time_col, voltage_col = fuzzy_find_columns(df)
        
        if time_col is None or voltage_col is None:
            # Try to infer: first numeric column might be time, second might be voltage
            numeric_cols = df.select_dtypes(include=[np.number]).columns.tolist()
            if len(numeric_cols) >= 2:
                time_col = numeric_cols[0]
                voltage_col = numeric_cols[1]
            else:
                return None, None, None
        
        # Extract data
        time = df[time_col].values
        voltage = df[voltage_col].values
        
        # Extract metadata from filename or header comments
        metadata = {}
        
        # Try to read header comments (if file has # comments)
        try:
            with open(file_path, 'r') as f:
                first_lines = [f.readline() for _ in range(20)]
                for line in first_lines:
                    if '#' in line or '//' in line:
                        if 'sampling' in line.lower() or 'rate' in line.lower():
                            # Extract sampling rate
                            match = re.search(r'(\d+(?:\.\d+)?)\s*(?:kHz|Hz|kHz)', line.lower())
                            if match:
                                metadata['sampling_rate'] = float(match.group(1))
        except:
            pass
        
        return time, voltage, metadata
        
    except Exception as e:
        print(f"Error parsing PatchMaster CSV {file_path}: {e}")
        return None, None, None


def extract_patchmaster_metadata(filename):
    """Extract metadata from PatchMaster/HEKA filename patterns"""
    filename_lower = filename.lower()
    
    # Extract cell ID
    cell_patterns = [
        r'cell[_\s]*(\d+)',
        r'cell(\d+)',
        r'c(\d+)',
        r'^(\d+)_cell',
    ]
    
    cell_id = "Cell_Unknown"
    for pattern in cell_patterns:
        match = re.search(pattern, filename_lower)
        if match:
            cell_id = f"Cell_{match.group(1)}"
            break
    
    # Extract frequency
    freq_patterns = [
        r'(\d+\.?\d*)\s*hz',
        r'(\d+\.?\d*)hz',
        r'_(\d+\.?\d*)hz',
        r'(\d+\.?\d*)_hz',
    ]
    
    frequency = "1.0"
    for pattern in freq_patterns:
        match = re.search(pattern, filename_lower)
        if match:
            freq_val = float(match.group(1))
            if abs(freq_val - 0.5) < 0.1:
                frequency = "0.5"
            elif abs(freq_val - 1.0) < 0.1:
                frequency = "1.0"
            elif abs(freq_val - 2.0) < 0.1:
                frequency = "2.0"
            elif abs(freq_val - 3.0) < 0.1:
                frequency = "3.0"
            elif abs(freq_val - 4.0) < 0.1:
                frequency = "4.0"
            elif abs(freq_val - 5.0) < 0.1:
                frequency = "5.0"
            else:
                frequency = f"{freq_val:.1f}"
            break
    
    # Extract drug/condition
    drug = "None"
    for drug_name in COMMON_DRUGS:
        if drug_name.lower() != 'none' and drug_name.lower() in filename_lower:
            drug = drug_name
            break
    
    # Extract trace number
    trace_match = re.search(r'trace[_\s]*(\d+)|_(\d+)(?:\.csv$)', filename_lower)
    trace_number = trace_match.group(1) if trace_match and trace_match.group(1) else (trace_match.group(2) if trace_match else "0")
    
    return {
        'cell_id': cell_id,
        'frequency': frequency,
        'drug': drug,
        'trace_number': trace_number,
        'source': 'PatchMaster'
    }


# ============================================================================
# Main Application Entry Point
# ============================================================================

def main():
    root = tk.Tk()
    app = APEXPlatformEnhanced(root)
    
    try:
        root.iconbitmap(default='apex_icon.ico')
    except:
        pass
    
    root.mainloop()


if __name__ == "__main__":
    main()