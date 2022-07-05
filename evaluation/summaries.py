import numpy as np


def three_num(data):
    """90, 95, and 99th percentiles."""
    # Taken from Wikipedia
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [90, 95, 99], method='midpoint')


def five_num(data):
    """5xth percentiles."""
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [i for i in range(0, 101, 25)], method='midpoint')


def twenty_num(data):
    """5xth percentiles."""
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [i for i in range(0, 101, 5)], method='midpoint')
