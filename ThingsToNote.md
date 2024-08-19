There are a few miscellaneous things you might want to know when continuing this project.

The following is in no particular order:
1. From my understanding, if qubits are allocated by a use block, not a use statement, then they are deallocated as soon as you leave the block. This might make things a little cleaner and maybe run faster. Most of the findOrderofAMod____ operations don't do this but findOrderofAModL_Error() does and it might be worth changing all of them to do that.

2. Before doing any of the modular multiplication, the y register is set to equal 1. Sam and I theorized that since the important thing is that the a^|x> mod n has a periodic nature, then we should be able to set the y register to anything non-zero and it should work. I tested it briefly with small n = 35, 77 and it seemed to be unchanged however it might be worth testing more extensively and with larger n.

3. Almost all the comments in the MicrosoftQuantumCryptoError library are copied over from the MicrosoftQuantumCrypto library. I also added comments about missing operation that weren't copied over since they weren't required. 

4. BasicsError.qs has quite a few more of my comments since I added things to the file that aren't in Basics.qs and I didn't know where to put them.

5. ArithmeticTestsError.qs contains a lot of tests that pass and a lot of ExhaustiveReversible tests that take literally forever so I didn't bother waiting to see if they passed

6. The current system of introducing errors is using Qubit_Error type which has an Int[] with probabilities that different types of errors occur before applying the intended gate. CUrrently, if you get unlucky, multiple types of errors can occur before the intended gate. Currently prob = int[] has length 2 with prob[0] is for applying an X gate before intended, and prob[1] is for applying Z gate. If you want to add more types of errors, change the get_Prob() functions and causeError operations in SECTION 1

7. I didn't really write comments for the very basic gates where it's the same thing except apply a different gate at the very end

8. The recycled versions of findOrderofAMod go from most significant bit to least so you can potentially skip on a lot of quantum computation by cutting off at some point and just classically checking every number within some epsilon of the return value.