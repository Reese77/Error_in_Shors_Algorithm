# Error_in_Shors_Algorithm
My URA project during Summer 2024 at the University of Waterloo to investigate the effect that small errors have in the output of Shor's Algorithm
Supervised by Samuel Jacques

HOW TO RUN:
I use VSCode with the Azure Quantum Development Kit (QDK) extension to run everything. Not sure how I would run it without. You would have to get some compiler. The nice thing about running it in VSCode is that right about your @EntryPoint() method, in this case Main() there are buttons to run the program once, run it n times and make a histogram of the results, and estimate, debug, or look at the circuit. I haven't played around with the last 3 so I don't know how they work. Sometimes after making changes to the code, those buttons disappear but if you wait a bit or sometimes just delete and retype a character, it will show up.

HOW TO USE:
Main.qs has a Main() operation that is used for basically everything. I have 4 options which are commented on in greater detail in Main.qs

1. Recreates the histogram idea but prints them to the console so you can copy paste and add to a dataset if you want. You change the len variable to adjust how many times you want to repeat. You can read the comments there for more details.

2. Runs the code just once and returns a bool for if the (measured value)/2^n is a "close approximate" of some integer/order. The order is precomputed naively which will be slow for larger numbers.

3. This takes the measured value and puts it through classical post-processing via continued fraction expansion to actually try and find the order. If it can't it will return -(measured value). If the post-procecssing works, the order it finds will obviously be positive so it's easy to distinguish between a real order candidate and if the program failed to find one. 

4. This just returns a tuple of (order candidate, measured value)


You are free to play around with this depending on what it is you're looking for. Personally, I think option 2 is best since if what you get is a "close approximate" you should almost always recover it in post-processing unless there is a large common factor in the fraction.

In the libraries folder, there is a folder called MicrosoftQuantumCrypto which was copied from:
https://github.com/microsoft/QuantumEllipticCurves/

There is also a folder called MicrosoftQuantumCryptoError which has copies of many of the files, functions, and operations that use the Qubit_Error type instead of normal Qubits