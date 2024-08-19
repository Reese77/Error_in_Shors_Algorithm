I believe all the setup is complete for this entire project. There are 2 things left to do

1. See how well the algorithm works for larger and larger numbers

2. Tweak the X and Z probabilities on the X and Y registers, Ancilla and Control qubits and observe how the probability of success is affected. You can measure probability of success by if it outputs a valid order candidate or by the minimum distance of the qftres to an integer multiple of 1/order. where you precomputed the order. I like the latter and if qftres is within 1/order^2 of integer/order since that is what is considered a close enough approximate.

I have a few theories about what I think is more important or not.
1. I think in the non-recycled version, any errors to the y register after the multiplication while measuring shouldn't have any effect. Though I imagine errors during the multiplication would be unrecoverable. In the recycled version, y isn't even measured so I think error-correction will be very important

2. 