load('recurrence.sage')

R = Recurrence(QQ) # Ring of recurrent sequences over Q


F = R.fib()   # Fibonacci sequence
F.show()      # Displays F
print F[3:12] # Display some elements of F

alt = R.exp(-1)  # Alternating sequence (-1)^n
print F.shift(1)*F.shift(-1) - F^2 == alt  # Verify the identity F_{n+1}*F_{n-1} - F_n^2 == (-1)^n

# Add more examples