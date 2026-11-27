from msgpy import N
def degen(x):
    if x[0] in 'TN': return False
    if x[0] == 'P' and x[1] == N and x[2] == N: return True
    return degen(x[1]) or degen(x[2])
