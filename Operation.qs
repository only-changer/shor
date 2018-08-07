namespace Quantum.shor
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;

	newtype Um = ((Int, Qubit[]) => ():Adjoint,Controlled);

	operation Set (desired: Result, q1: Qubit) : ()
    {
		//This fucntion is used to flip the qubit,if it is not equal to the expected.
        body
        {
            let current = M(q1);

            if (desired != current)
            {
                X(q1);
            } 
        }
    }

	operation Sum (a1 : Qubit , a2 : Qubit , a3 : Qubit) : ()
	{
		//This function is used for sum.
		body
		{
			CNOT(a2 , a3);
			CNOT(a1 , a3);
		}
	}
	operation Carry(a1 : Qubit , a2 : Qubit , a3 : Qubit , a4 : Qubit) : ()
	{
		//This function is used for carry.
		body
		{
			CCNOT(a2 , a3 , a4);
			CNOT(a2 , a3);
			CCNOT(a1 , a3 , a4);
		}
	}
	operation inCarry(a1 : Qubit , a2 : Qubit , a3 : Qubit , a4 : Qubit) : ()
	{
		//This function is an inverse function of Carry.
		body
		{
			CCNOT(a1 , a3 , a4);	
			CNOT(a2 , a3);
			CCNOT(a2 , a3 , a4);
		}
	}
	operation Adder(a : Qubit[] , b : Qubit[] , c : Qubit[] , d : Qubit) :()
	{
		//This function returns the result of (a + b).
		//d is used for carry.
		body
		{
			for (i in 0..3)
			{
				Carry(c[i] , a[i] , b[i] , c[i + 1]);
			}
			Carry(c[4] , a[4] , b[4] , d);
			CNOT(a[4] , b[4]);
			Sum(c[4] , a[4] , b[4]);
			for (i in 0..3)
			{
				inCarry(c[3 - i] , a[3 - i] , b[3 - i] , c[4 - i]);
				Sum(c[3 - i] , a[3 - i] , b[3 - i]);
			}
		}
	}
	operation inAdder(a : Qubit[] , b : Qubit[] , c : Qubit[] , d : Qubit) :()
	{
		//This function is an inverse function of Adder
		body
		{
			for (i in 0..3)
			{
				Sum(c[i] , a[i] , b[i]);
				Carry(c[i] , a[i] , b[i] , c[i + 1]);
			}
			Sum(c[4] , a[4] , b[4]);	
			CNOT(a[4] , b[4]);
			inCarry(c[4] , a[4] , b[4] , d);
			for (i in 0..3)
			{
				inCarry(c[3 - i] , a[3 - i] , b[3 - i] , c[4 - i]);
			}
		}
	}
	operation Add_Mod (a : Qubit[] , b : Qubit[] , n : Qubit[]) : ()
	{
		//This function returns the result of (a + b) mod n
		body
		{
			using (c = Qubit[5])
			{
				for (i in 0..4)
				{
					Set(Zero, c[i]);
				}	
				using (d = Qubit[1])
				{
					Set(Zero , d[0]);
					using (v = Qubit[1])
					{
						Set(Zero , v[0]);
						using (o = Qubit[1])
						{
							Set(One , o[0]);
							Adder(a , b , c , d[0]);
							inAdder(n , b , c , d[0]);
							CNOT(o[0] , d[0]);
							CNOT(d[0] , v[0]);
							CNOT(o[0] , d[0]);
							for (i in 0..4)
							{	
								CNOT(v[0] , n[i]);
							}
							Adder(n , b , c , d[0]);
							for (i in 0..4)
							{
								CNOT(v[0] , n[i]);
							}
							inAdder(a , b , c , d[0]);
							CNOT(d[0] , v[0]);
							Adder(a , b , c , d[0]);
							ResetAll(o);
						}
						ResetAll(v);
					}
					ResetAll(d);
				}
				ResetAll(c);
			}
		}
	}

	function Expmod(radix : Int , cleanedPeriod : Int ,modulus : Int):(Int)
	{
		//The function returns xᵖ mod N . 
		//We assume that N,x are positive and power is non-negative.
        mutable x = radix;
        mutable ans = 1;
        mutable k = cleanedPeriod;

        for(i in 0..5)
		{
            if(k % 2 == 1)
			{
                set ans = ans * x % modulus;
            }
            set x = x * x % modulus;
            set k = k / 2;
        }
        return ans;
    }

	operation myQFT ( qs: BigEndian) : () 
	{
		//Performs the Quantum Fourier Transform on a quantum register containing an integer in the big-endian representation.
        body 
		{
            let n= Length(qs);
            for (i in 0..(n - 1) ) 
			{
                for (j in 0..(i-1)) 
				{
                    if ( (i-j) < n ) 
					{
                        (Controlled R1Frac)( [qs[i]], (1, i - j, qs[j]) );
                    }
                }
                H(qs[i]);
            }
            for( i in 0 ..(n / 2 - 1 ))
			{
                SWAP(qs[i],qs[n - i - 1 ]);
            }
        }
        adjoint auto
        controlled auto
        controlled adjoint auto
    }
	
	 operation myQPE( oracle : Um,  targetState : Qubit[], controlRegister : BigEndian) : () 
    {
		// Performs the quantum phase estimation algorithm for a given oracle U and targetState,
		// reading the phase into a big-endian quantum register.
        body 
		{
            let n = Length(controlRegister);
			for (i in 0..(n - 1))
			{
				H(controlRegister[i]);
			}
            for (j in 0..(n - 1)) 
			{
                let control = controlRegister[j];
                let power = 2 ^ (n - j - 1);
                (Controlled oracle)([control], (power, targetState));
            }
            (Adjoint myQFT)(controlRegister);
        }
		adjoint auto
		controlled auto
		controlled adjoint auto
    }

	operation PowerOracle (radix: Int, modulus: Int, power: Int, target: Qubit[]) : ()
	{
		//This function is used for denoting modulus by N and constMultiplier by a then this operation implements a unitary 
		//defined by the following map on computational basis: |y⟩ ↦ |a⋅y (mod N) ⟩, for all y between 0 and N - 1
		body
		{
			ModularMultiplyByConstantLE( Expmod(radix,power,modulus), modulus, LittleEndian(target));
		}
		adjoint auto
		controlled auto
		adjoint controlled auto
	}

	operation shor(radix: Int, modulus: Int ) : (Int)
    {
		//This is the core function , which achieves the shor's algorithm
        body
        {
			mutable measuredPeriod = 0;
			let registersize = 2*BitSize(modulus)+1;

			using ( targetState = Qubit[BitSize(modulus)] )
			{
				using ( controlRegister = Qubit[registersize] )
				{
					IntegerIncrementLE( 1 , LittleEndian(targetState) );
					myQPE(Um(PowerOracle(radix,modulus,_,_)) , LittleEndian(targetState) , BigEndian(controlRegister) );
					set measuredPeriod = MeasureIntegerBE( BigEndian(controlRegister) );
					ResetAll(targetState);
				}
			}
		    let cleanedPeriod = AbsI(Snd( ContinuedFractionConvergent( Fraction(measuredPeriod, 2^(registersize)) , modulus ) )) ;			
			return Expmod(radix, cleanedPeriod/2 , modulus ); 
		}
    }
}