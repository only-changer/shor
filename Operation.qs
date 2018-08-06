namespace Quantum.shor
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Testing;
    open Microsoft.Quantum.Extensions.Math;

	newtype Um = ((Int, Qubit[]) => ():Adjoint,Controlled);

	function Expmod(radix : Int , cleanedPeriod : Int ,modulus : Int):(Int)
	{
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
        body 
		{
            let n= Length(qs);
            for (i in 0 .. (n - 1) ) 
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
            SwapReverseRegister(qs);
        }
        adjoint auto
        controlled auto
        controlled adjoint auto
    }

	 operation QPE( oracle : Um,  targetState : Qubit[], controlRegister : BigEndian) : ()
    {
        body 
		{
            let n = Length(controlRegister);
			for (i in 0..(n - 1))
			{
				H(controlRegister[i]);
			}
            for (idxControlQubit in 0..(n - 1)) 
			{
                let control = controlRegister[idxControlQubit];
                let power = 2 ^ (n - idxControlQubit - 1);
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
        body
        {
			mutable measuredPeriod = 0;
			let registersize = 2*BitSize(modulus)+1;

			using ( targetState = Qubit[BitSize(modulus)] )
			{
				using ( controlRegister = Qubit[registersize] )
				{
					IntegerIncrementLE( 1 , LittleEndian(targetState) );
					QPE(Um(PowerOracle(radix,modulus,_,_)) , LittleEndian(targetState) , BigEndian(controlRegister) );
					set measuredPeriod = MeasureIntegerBE( BigEndian(controlRegister) );
					ResetAll(targetState);
				}
			}
		    let cleanedPeriod = AbsI(Snd( ContinuedFractionConvergent( Fraction(measuredPeriod, 2^(registersize)) , modulus ) )) ;			
			return Expmod(radix, cleanedPeriod/2 , modulus ); 
		}
    }
}