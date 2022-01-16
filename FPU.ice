algorithm fpufast(
    input   uint2   function3,
    input   uint5   function7,
    input   uint32  sourceReg1,
    input   uint32  sourceReg1F,
    input   uint32  sourceReg2F,
    input   uint4   classA,
    input   uint4   classB,

    output  uint32  result,
    output  uint1   frd,
    input   uint5   FPUflags,
    output  uint5   FPUnewflags
) <autorun> {
    // GENERATE LESS AND EQUAL FLAGS FOR MIN/MAX AND COMPARISONS
    floatcompare FPUlteq( a <: sourceReg1F, b <: sourceReg2F, classA <: classA, classB <: classB );
    floatminmax FPUminmax( sourceReg1F <: sourceReg1F, sourceReg2F <: sourceReg2F, classA <: classA, classB <: classB, less <: FPUlteq.less, function3 <: function3[0,1] );
    floatcomparison FPUcompare( sourceReg1F <: sourceReg1F, sourceReg2F <: sourceReg2F, classA <: classA, classB <: classB, less <: FPUlteq.less, equal <: FPUlteq.equal, function3 <: function3[0,2], );
    floatclassify FPUclass( sourceReg1F <: sourceReg1F, classA <: classA );
    floatsign FPUsign( function3 <: function3[0,2], sourceReg1F <: sourceReg1F, sourceReg2F <: sourceReg2F );

    always_after {
        switch( function7[3,2] ) {
            case 2b00: {
                // FMIN.S FMAX.S FSGNJ.S FSGNJN.S FSGNJX.S
                frd = 1; result = function7[0,1] ? FPUminmax.result : FPUsign.result; FPUnewflags = FPUflags | ( function7[0,1] ? FPUminmax.flags : 0 );
            }
            case 2b10: {
                // FEQ.S FLT.S FLE.S
                frd = 0; result = FPUcompare.result; FPUnewflags = FPUflags | FPUcompare.flags;
            }
            default: {
                // FCLASS.S FMV.X.W FMV.W.X
                frd = function7[1,1]; result = function7[1,1] ? sourceReg1 : function3[0,1] ? FPUclass.classification : sourceReg1F; FPUnewflags = FPUflags;
            }
        }
    }
}

algorithm fpuslow(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint5   opCode,
    input   uint5   function7,
    input   uint1   rs2,
    input   uint32  sourceReg1,
    input   uint32  abssourceReg1,
    input   uint32  sourceReg1F,
    input   uint32  sourceReg2F,
    input   uint32  sourceReg3F,
    input   uint4   classA,
    input   uint4   classB,
    input   uint4   classC,

    output  uint32  result,
    output  uint1   frd,
    input   uint5   FPUflags,
    output  uint5   FPUnewflags
) <autorun,reginputs> {
    floatcalc FPUcalculator( sourceReg1F <: sourceReg1F, sourceReg2F <: sourceReg2F, sourceReg3F <: sourceReg3F,
                                classA <: classA, classB <: classB, classC <: classC,
                                opCode <: opCode, function7 <: function7 );
    floatconvert FPUconvert( sourceReg1 <: sourceReg1, abssourceReg1 <: abssourceReg1, sourceReg1F <: sourceReg1F, classA <: classA, direction <: function7[1,1], rs2 <: rs2, );

    FPUcalculator.start := start & ~( opCode[2,1] & function7[4,1] );

    while(1) {
        if( start ) {
            busy = 1;
            if( opCode[2,1] & function7[4,1] ) {
                // FCVT.W.S FCVT.WU.S  FCVT.S.W FCVT.S.WU
                if( function7[1,1] ) { frd = 1; ++: } else { frd = 0; } result = FPUconvert.result; FPUnewflags = FPUflags | FPUconvert.flags;
            } else {
                // FMADD.S FMSUB.S FNMSUB.S FNMADD.S FADD.S FSUB.S FMUL.S FDIV.S FSQRT.S
                frd = 1; while( FPUcalculator.busy ) {} result = FPUcalculator.result; FPUnewflags = FPUflags | FPUcalculator.flags;
            }
            busy = 0;
        }
    }
}

// CONVERSION BETWEEN FLOAT AND SIGNED/UNSIGNED INTEGERS
algorithm floatconvert(
    input   uint1   direction,
    input   uint1   rs2,
    input   uint32  sourceReg1,
    input   uint32  abssourceReg1,
    input   uint32  sourceReg1F,
    input   uint4   classA,

    output  uint5   flags,
    output  uint32  result
) <autorun,reginputs> {
    inttofloat FPUfloat( a <: sourceReg1, absa <: abssourceReg1, dounsigned <: rs2[0,1] );
    floattoint FPUint( a <: sourceReg1F, classA <: classA );
    floattouint FPUuint( a <: sourceReg1F, classA <: classA );

    always_after {
        // FCVT.S.W FCVT.S.WU FCVT.W.S FCVT.WU.S
        result = direction ? FPUfloat.result : rs2 ? FPUuint.result : FPUint.result; flags = direction ? FPUfloat.flags : rs2 ? FPUuint.flags : FPUint.flags;
    }
}

// FPU CALCULATION BLOCKS FUSED ADD SUB MUL DIV SQRT
algorithm floatcalc(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint5   opCode,
    input   uint5   function7,
    input   uint32  sourceReg1F,
    input   uint32  sourceReg2F,
    input   uint32  sourceReg3F,
    input   uint4   classA,
    input   uint4   classB,
    input   uint4   classC,

    output  uint5   flags,
    output  uint32  result,
) <autorun,reginputs> {
    // CLASSIFY THE RESULT OF MULTIPLICATION
    classifyF classM( a <: FPUmultiply.result );

    // ADD/SUB/MULT have changeable inputs due to 2 input and 3 input fused operations
    floataddsub FPUaddsub( cOF <: MAKERESULT.OF, cUF <: MAKERESULT.UF, f32 <: MAKERESULT.f32 );
    floatmultiply FPUmultiply( b <: sourceReg2F, classA <: classA, classB <: classB, cOF <: MAKERESULT.OF, cUF <: MAKERESULT.UF, f32 <: MAKERESULT.f32 );
    floatdivide FPUdivide( a <: sourceReg1F, b <: sourceReg2F, classA <: classA, classB <: classB, cOF <: MAKERESULT.OF, cUF <: MAKERESULT.UF, f32 <: MAKERESULT.f32 );
    floatsqrt FPUsqrt( a <: sourceReg1F, classA <: classA, cOF <: MAKERESULT.OF, cUF <: MAKERESULT.UF, f32 <: MAKERESULT.f32 );

    // NORMALISE RESULT OF ADD SUB DIV
    normalise24 DONORMAL( exp <: FPUaddsub.tonormaliseexp );

    // ROUNDING AND COMBINING OF FINAL RESULTS
    doroundcombine MAKERESULT();

    // NEW FPU FLAGS
    uint5   FNFas <:: FPUaddsub.flags & 5b00110;    uint5   FNFm <:: FPUmultiply.flags & 5b00110;       uint5   FNFd <:: FPUdivide.flags & 5b01110;
    uint5   FNFs <:: FPUsqrt.flags & 5b00110;       uint5   FNFfused <:: ( FPUmultiply.flags & 5b10110 ) | ( FPUaddsub.flags & 5b00110 );

    DONORMAL.bitstream := opCode[2,1] & ( &function7[0,2] ) ? FPUdivide.tonormalisebitstream : FPUaddsub.tonormalisebitstream;
    FPUaddsub.start := 0; FPUmultiply.start := 0; FPUdivide.start := 0; FPUsqrt.start := 0;

    // PREPARE INPUTS FOR ADDITION/SUBTRACTION AND MULTIPLICATION
    // CONTROL INPUTS TO ROUNDING AND COMBINING
    always {
        if( opCode[2,1] ) {
            FPUaddsub.a = sourceReg1F; FPUaddsub.b = { function7[0,1] ^ sourceReg2F[31,1], sourceReg2F[0,31] };
            FPUaddsub.classA = classA; FPUaddsub.classB = classB;
            FPUmultiply.a = sourceReg1F;
        } else {
            FPUaddsub.a = FPUmultiply.result; FPUaddsub.b = { opCode[0,1] ^ sourceReg3F[31,1], sourceReg3F[0,31] };
            FPUaddsub.classA = classM.class; FPUaddsub.classB = classC;
            FPUmultiply.a = { opCode[1,1] ^ sourceReg1F[31,1], sourceReg1F[0,31] };
        }
        if( FPUaddsub.busy ) { MAKERESULT.exponent = DONORMAL.newexponent; MAKERESULT.bitstream = DONORMAL.normalfraction; MAKERESULT.sign = FPUaddsub.resultsign; }
        if( FPUmultiply.busy ) { MAKERESULT.exponent = FPUmultiply.productexp; MAKERESULT.bitstream = FPUmultiply.normalfraction; MAKERESULT.sign = FPUmultiply.productsign; }
        if( FPUdivide.busy ) { MAKERESULT.exponent = FPUdivide.quotientexp; MAKERESULT.bitstream = DONORMAL.normalfraction; MAKERESULT.sign = FPUdivide.quotientsign; }
        if( FPUsqrt.busy ) { MAKERESULT.exponent = FPUsqrt.squarerootexp; MAKERESULT.bitstream = FPUsqrt.normalfraction; MAKERESULT.sign = 0; }
    }

    while(1) {
        if( start ) {
            busy = 1;
            if( opCode[2,1] ) {
                // NON 3 REGISTER FPU OPERATIONS
                switch( function7[0,2] ) {
                    default: {
                        // FADD.S FSUB.S
                        FPUaddsub.start = 1; while( FPUaddsub.busy ) {} result = FPUaddsub.result; flags = FNFas;
                    }
                    case 2b10: {
                        // FMUL.S
                        FPUmultiply.start = 1; while( FPUmultiply.busy ) {} result = FPUmultiply.result; flags = FNFm;
                    }
                    case 2b11: {
                        if( function7[3,1] ) {
                            // FSQRT.S
                            FPUsqrt.start = 1; while( FPUsqrt.busy ) {} result = FPUsqrt.result; flags = FNFs;
                        } else {
                            // FDIV.S
                            FPUdivide.start = 1; while( FPUdivide.busy ) {} result = FPUdivide.result; flags = FNFd;
                        }
                    }
                }
            } else {
                // 3 REGISTER FUSED FPU OPERATIONS - MULTIPLY then ADD/SUB
                FPUmultiply.start = 1; while( FPUmultiply.busy ) {} FPUaddsub.start = 1; while( FPUaddsub.busy ) {} result = FPUaddsub.result;
                flags = FNFfused;
            }
            busy = 0;
        }
    }
}

algorithm floatclassify(
    input   uint32  sourceReg1F,
    input   uint4   classA,
    output  uint10  classification
) <autorun> {
    uint4   bit = uninitialised;

    always_after {
        if( |classA ) {
            // INFINITY, NAN OR ZERO
            onehot( classA ) {
                case 0: { bit = ~|sourceReg1F[0,23] ? fp32( sourceReg1F ).sign ? 3 : 4 : fp32( sourceReg1F ).sign ? 2 : 5; }
                case 1: { bit = 9; }
                case 2: { bit = 8; }
                case 3: { bit = fp32( sourceReg1F ).sign ? 0 : 7; }
            }
        } else {
            // NUMBER
            bit = fp32( sourceReg1F ).sign ? 1 : 6;
        }
        classification = 1 << bit;
    }
}

algorithm floatminmax(
    input   uint1   less,
    input   uint1   function3,
    input   uint32  sourceReg1F,
    input   uint32  sourceReg2F,
    input   uint4   classA,
    input   uint4   classB,
    output  uint5   flags,
    output  uint32  result
) <autorun> {
    uint1   NAN <:: ( classA[2,1] | classB[2,1] ) | ( classA[1,1] & classB[1,1] );

    flags := { NAN, 4b0000 };
    always_after {
        result = NAN ? 32h7fc00000 : classA[1,1] ? ( classB[1,1] ? 32h7fc00000 : sourceReg2F ) : classB[1,1] | ( function3 ^ less ) ? sourceReg1F : sourceReg2F;
    }
}

// COMPARISONS
algorithm floatcomparison(
    input   uint1   less,
    input   uint1   equal,
    input   uint2   function3,
    input   uint32  sourceReg1F,
    input   uint32  sourceReg2F,
    input   uint4   classA,
    input   uint4   classB,
    output  uint5   flags,
    output  uint1   result
) <autorun> {
    uint1   NAN <:: ( classA[1,1] | classA[2,1] | classB[1,1] | classB[2,1] );
    uint4   comparison <:: { 1b0, equal, less, less | equal };
    flags := { function3[1,1] ? ( classA[2,1] | classB[2,1] ) : NAN, 4b0000 };
    always_after {
        result = ~NAN & comparison[ function3, 1 ];
    }
}

algorithm floatsign(
    input   uint2   function3,
    input   uint32  sourceReg1F,
    input   uint32  sourceReg2F,
    output  uint32  result,
) <autorun> {
    uint1   sign <:: function3[1,1] ? sourceReg1F[31,1] ^ sourceReg2F[31,1] : function3[0,1] ^ sourceReg2F[31,1];
    always_after {
        result = { sign, sourceReg1F[0,31] };
    }
}


// Rob Shelton ( @robng15 Twitter, @rob-ng15 GitHub )
// Simple 32bit FPU calculation/conversion routines
// Designed for as small as FPGA usage as possible,
// not for speed.
//
// Copyright (c) 2021 Rob Shelton
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//
// Donated to Silice by @sylefeb
// MIT license, see LICENSE_MIT in Silice repo root
//
// Parameters for calculations: ( 32 bit float { sign, exponent, mantissa } format )
// addsub, multiply and divide a and b ( as floating point numbers ), addsub flag == 0 for add, == 1 for sub
//
// Parameters for conversion:
// intotofloat a as 32 bit integer, dounsigned == 1 dounsigned, == 0 signed conversion
// floattouint and floattoint a as 32 bit float
//
// Control:
// start == 1 to start operation
// busy gives status, == 0 not running or complete, == 1 running
//
// Output:
// result gives result of conversion or calculation
//
// NB: Error states are those required by Risc-V floating point

// CLZ CIRCUITS - TRANSLATED BY @sylefeb
// From recursive Verilog module
// https://electronics.stackexchange.com/questions/196914/verilog-synthesize-high-speed-leading-zero-count

// Create a LUA pre-processor function that recursively writes
// circuitries counting the number of leading zeros in variables
// of decreasing width.
// Note: this could also be made in-place without wrapping in a
// circuitry, directly outputting a hierarchical set of trackers (<:)
$$function generate_clz(name,w_in,recurse)
$$ local w_out = clog2(w_in)
$$ local w_h   = w_in//2
$$ if w_in > 2 then generate_clz(name,w_in//2,1) end
circuitry $name$_$w_in$ (input in,output out)
{
$$ if w_in == 2 then
   out = !in[1,1];
$$ else
   uint$clog2(w_in)-1$ half_count = uninitialized;
   uint$w_h$           lhs        <: in[$w_h$,$w_h$];
   uint$w_h$           rhs        <: in[    0,$w_h$];
   uint$w_h$           select     <: left_empty ? rhs : lhs;
   uint1               left_empty <: ~|lhs;
   (half_count) = $name$_$w_h$(select);
   out          = {left_empty,half_count};
$$ end
}
$$end

// Produce a circuit for 32 bits numbers ( and 16, 8, 4, 2 )
$$generate_clz('clz_silice',32)

// BITFIELD FOR FLOATING POINT NUMBER - IEEE-754 32 bit format
bitfield fp32{
    uint1   sign,
    uint8   exponent,
    uint23  fraction
}

// IDENTIFY infinity, signalling NAN, quiet NAN, ZERO
algorithm classifyF(
    input   uint32  a,
    output  uint4   class
) <autorun> {
    // CHECK FOR 8hff ( signals INF/NAN )
    uint1   expFF <:: &fp32(a).exponent;
    uint1   NAN <:: expFF & a[22,1];
    always_after {
        class = { expFF & ~a[22,1], NAN & a[21,1], NAN & ~a[21,1], ~|( fp32(a).exponent ) };
    }
}

// REFERENCE, NOT USED IN THIS MODULE
bitfield floatingpointflags{
    uint1   IF,     // infinity as an argument
    uint1   NN,     // NaN as an argument
    uint1   NV,     // Result is not valid,
    uint1   DZ,     // Divide by zero
    uint1   OF,     // Result overflowed
    uint1   UF,     // Result underflowed
    uint1   NX      // Not exact ( integer to float conversion caused bits to be dropped )
}

// NORMALISE A 48 BIT MANTISSA SO THAT THE MSB IS ONE, FOR ADDSUB ALSO DECREMENT THE EXPONENT FOR EACH SHIFT LEFT
// EXTRACT THE 24 BITS FOLLOWING THE MSB (1.xxxx) FOR ROUNDING
algorithm clz48(
    input   uint48  bitstream,
    output! uint6   count
) <autorun> {
    uint16  bitstreamh <:: bitstream[32,16];        uint32  bitstreaml <:: bitstream[0,32];
    uint6   clz = uninitialised;
    always_after {
        if( ~|bitstreamh ) {
            ( clz ) = clz_silice_32( bitstreaml );
            count = 16 + clz;
        } else {
            ( count ) = clz_silice_16( bitstreamh );
        }
    }
}
// NORMALISE RESULT FOR ADD SUB DIVIDE
algorithm normalise24(
    input   int10   exp,
    input   uint48  bitstream,
    output  int10   newexponent,
    output  uint24  normalfraction
) <autorun,reginputs> {
    // COUNT LEADING ZEROS
    clz48 CLZ48( bitstream <: bitstream );          uint48  temporary <:: bitstream << CLZ48.count;
    always_after {
        normalfraction = temporary[23,24];
        newexponent = exp - CLZ48.count;
    }
}

// NORMALISE RESULT FOR MULTIPLICATION AND SQUARE ROOT
algorithm fastnormal24(
    input   uint48  tonormal,
    output  uint24  normalfraction
) <autorun> {
    always_after {
        normalfraction = tonormal[ tonormal[47,1] ? 23 : 22,24 ];
    }
}

// ROUND 23 BIT FRACTION FROM NORMALISED FRACTION USING NEXT TRAILING BIT
// ADD BIAS TO EXPONENT AND ADJUST EXPONENT IF ROUNDING FORCES
// COMBINE COMPONENTS INTO FLOATING POINT NUMBER - USED BY CALCULATIONS
// UNDERFLOW return 0, OVERFLOW return infinity
algorithm doroundcombine(
    input   uint1   sign,
    input   uint24  bitstream,
    input   int10   exponent,
    output  uint1   OF,
    output  uint1   UF,
    output  uint32  f32
) <autorun,reginputs> {
    uint23  roundfraction <:: bitstream[1,23] + bitstream[0,1];
    int10   newexponent = uninitialised;
    always_after {
        newexponent = ( ( ~|roundfraction & bitstream[0,1] ) ? 128 : 127 ) + exponent;
        OF = ( newexponent > 254 ); UF = newexponent[9,1];
        f32 = UF ? 0 : { sign, OF ? 31h7f800000 : { newexponent[0,8], roundfraction } };
    }
}

// CONVERT SIGNED/UNSIGNED INTEGERS TO FLOAT
// dounsigned == 1 for signed conversion (31 bit plus sign), == 0 for dounsigned conversion (32 bit)
algorithm prepitof(
    input   uint32  a,
    input   uint32  absa,
    input   uint1   dounsigned,
    output  uint1   sign,
    output  uint23  fraction,
    output  int10   exponent,
    output  uint1   NX
) <autorun> {
    // COUNT LEADING ZEROS - RETURNS NX IF NUMBER IS TOO LARGE, LESS THAN 8 LEADING ZEROS
    uint32  number <: sign ? absa : a;
    uint5   zeros = uninitialised;

    always_before {
        sign = ~dounsigned & a[31,1];
        ( zeros ) = clz_silice_32( number );
    }
    always_after {
        NX = ( ~|zeros[3,2] );
        fraction = NX ? number >> ( 8 - zeros ) : number << ( zeros - 8 );
        exponent = 158 - zeros;
    }
}
algorithm inttofloat(
    input   uint32  a,
    input   uint32  absa,
    input   uint1   dounsigned,
    output  uint7   flags,
    output  uint32  result
) <autorun> {
    prepitof PREP( a <: a, absa <: absa, dounsigned <: dounsigned );
    flags := { 6b0, PREP.NX };
    always_after {
        if( |a ) {
            result = { PREP.sign, PREP.exponent[0,8], PREP.fraction };
        } else {
            result = 0;
        }
    }
}

// BREAK DOWN FLOAT READY FOR CONVERSION TO INTEGER
algorithm prepftoi(
    input   uint32  a,
    output  int10   exp,
    output  uint32  unsignedfraction
) <autorun> {
    uint33  sig <:: ( exp < 24 ) ? { 9b1, fp32( a ).fraction, 1b0 } >> ( 23 - exp ) : { 9b1, fp32( a ).fraction, 1b0 } << ( exp - 24);
    always_after {
        exp = fp32( a ).exponent - 127;
        unsignedfraction = ( sig[1,32] + sig[0,1] );
    }
}

// CONVERT FLOAT TO SIGNED INTEGERS
algorithm floattoint(
    input   uint32  a,
    input   uint4   classA,
    output  uint7   flags,
    output  uint32  result
) <autorun> {
    uint1   NN <:: classA[2,1] | classA[1,1];       uint1   NV <:: ( PREP.exp > 30 ) | classA[3,1] | NN;

    // PREPARE THE CONVERSION
    prepftoi PREP( a <: a );

    flags := { classA[3,1], NN, NV, 4b0000 };
    always_after {
        if(classA[0,1] ) {
            result = 0;
        } else {
            if( classA[3,1] | NN ) {
                result = { ~NN & fp32( a ).sign, 31h7fffffff };
            } else {
                result = { fp32( a ).sign, NV ? 31h7fffffff : fp32( a ).sign ? -PREP.unsignedfraction : PREP.unsignedfraction };
            }
        }
    }
}

// CONVERT FLOAT TO UNSIGNED INTEGERS
algorithm floattouint(
    input   uint32  a,
    input   uint4   classA,
    output  uint7   flags,
    output  uint32  result
) <autorun> {
    uint1   NN <:: classA[2,1] | classA[1,1];       uint1   NV <:: ( PREP.exp > 31 ) | fp32( a ).sign | classA[3,1] | NN;

    // PREPARE THE CONVERSION
    prepftoi PREP( a <: a );

    flags := { classA[3,1], NN, NV, 4b0000 };
    always_after {
        if(classA[0,1] ) {
            result = 0;
        } else {
            if( classA[3,1] | NN ) {
                result = NN ? 32hffffffff : { {32{~fp32( a ).sign}} };
            } else {
                result = ( fp32( a ).sign ) ? 0 : NV ? 32hffffffff : PREP.unsignedfraction;
            }
        }
    }
}

// ADDSUB ADD/SUBTRACT TWO FLOATING POINT NUMBERS ( SUBTRACT ACHIEVED BY ALTERING SIGN OF SECOND INPUT )
algorithm equaliseexpaddsub(
    input   uint32  a,
    input   uint32  b,
    output  uint48  newsigA,
    output  uint48  newsigB,
    output  int10   resultexp,
) <autorun> {
    // BREAK DOWN INITIAL float32 INPUTS - SWITCH SIGN OF B IF SUBTRACTION
    uint48  sigA <:: { 2b01, fp32(a).fraction, 23b0 };                                                  uint48  sigB <:: { 2b01, fp32(b).fraction, 23b0 };
    int10   expA <:: fp32(a).exponent;                                                                  int10   expB <:: fp32(b).exponent;
    uint48  aligned = uninitialised;                                                                    uint1   AvB <:: ( expA < expB );

    always_after {
        aligned = ( AvB ? sigA : sigB ) >> ( AvB ? ( expB - expA ) : ( expA - expB ) );
        if( AvB ) {
            newsigA = aligned; newsigB = sigB;
        } else {
            newsigB = aligned; newsigA = sigA;
        }
        resultexp = ( AvB ? expB : expA ) - 126;
    }
}
algorithm dofloataddsub(
    input   uint1   signA,
    input   uint48  sigA,
    input   uint1   signB,
    input   uint48  sigB,
    output  uint1   resultsign,
    output  uint48  resultfraction
) <autorun> {
    uint48  sigAminussigB <:: sigA - sigB;          uint48  sigBminussigA <:: sigB - sigA;
    uint48  sigAplussigB <:: sigA + sigB;
    uint1   AvB <:: ( sigA > sigB );

    always_after {
        // PERFORM ADDITION HANDLING SIGNS
        if( ^{ signA, signB } ) {
            resultsign = signA ? AvB : ~AvB; resultfraction = signA ^ resultsign ? ( sigBminussigA ) : ( sigAminussigB );
        } else {
            resultsign = signA; resultfraction = sigAplussigB;
        }
    }
}

algorithm floataddsub(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint32  a,
    input   uint32  b,
    input   uint4   classA,
    input   uint4   classB,
    output  int10   tonormaliseexp,
    output  uint48  tonormalisebitstream,
    output  uint1   resultsign,
    input   uint1   cOF,
    input   uint1   cUF,
    input   uint32  f32,
    output  uint7   flags,
    output  uint32  result
) <autorun,reginputs> {
    // CLASSIFY THE INPUTS AND FLAG INFINITY, NAN, ZERO AND INVALID ( INF - INF )
    uint1   IF <:: ( classA[3,1] | classB[3,1] );
    uint1   NN <:: ( classA[2,1] | classA[1,1] | classB[2,1] | classB[1,1] );
    uint1   NV <:: ( classA[3,1] & classB[3,1]) & ( fp32( a ).sign ^ fp32( b).sign );
    uint1   OF = uninitialised;
    uint1   UF = uninitialised;

    // EQUALISE THE EXPONENTS
    equaliseexpaddsub EQUALISEEXP( a <: a, b <: b, resultexp :> tonormaliseexp );

    // PERFORM THE ADDITION/SUBTRACION USING THE EQUALISED FRACTIONS, 1 IS ADDED TO THE EXPONENT IN CASE OF OVERFLOW - NORMALISING WILL ADJUST WHEN SHIFTING
    dofloataddsub ADDSUB( signA <: fp32( a ).sign, sigA <: EQUALISEEXP.newsigA, signB <: fp32( b).sign, sigB <: EQUALISEEXP.newsigB, resultsign :> resultsign, resultfraction :> tonormalisebitstream );

    flags := { IF, NN, NV, 1b0, OF, UF, 1b0 };
    while(1) {
        if( start ) {
            busy = 1;
            OF = 0; UF = 0;
            switch( { IF | NN,classA[0,1] | classB[0,1] } ) {
                case 2b00: {
                    if( |ADDSUB.resultfraction ) {
                        ++: // ALLOW FOR NORMALISATION AND COMBINING OF FINAL RESULT
                        ++:
                        OF = cOF; UF = cUF; result = f32;
                    } else {
                        result = 0;
                    }
                }
                case 2b01: { result = (classA[0,1] & classB[0,1] ) ? 0 : ( classB[0,1] ) ? a : b; }
                default: {
                    switch( { IF, NN } ) {
                        case 2b10: { result = NV ? 32hffc00000 : classA[3,1] ? a : b; }
                        default: { result = 32hffc00000; }
                    }
                }
            }
            busy = 0;
        }
    }
}

// MULTIPLY TWO FLOATING POINT NUMBERS
algorithm prepmul(
    input   uint32  a,
    input   uint32  b,
    output  uint1   productsign,
    output  int10   productexp,
    output  uint24  normalfraction
) <autorun> {
    uint24  sigA <:: { 1b1, fp32( a ).fraction };   uint24  sigB <:: { 1b1, fp32( b ).fraction };
    uint48  product <:: sigA * sigB;

    fastnormal24 NORMAL( tonormal <: product, normalfraction :> normalfraction );

    always_after {
        productsign = fp32( a ).sign ^ fp32( b ).sign;
        productexp = fp32( a ).exponent + fp32( b ).exponent - ( product[47,1] ? 253 : 254 );
    }
}
algorithm floatmultiply(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint32  a,
    input   uint32  b,
    input   uint4   classA,
    input   uint4   classB,
    output  uint1   productsign,
    output  int10   productexp,
    output  uint24  normalfraction,
    input   uint1   cOF,
    input   uint1   cUF,
    input   uint32  f32,

    output  uint7   flags,
    output  uint32  result
) <autorun,reginputs> {
    // BREAK DOWN INITIAL float32 INPUTS AND FIND SIGN OF RESULT AND EXPONENT OF PRODUCT ( + 1 IF PRODUCT OVERFLOWS, MSB == 1 )
    // NORMALISE THE RESULTING PRODUCT AND EXTRACT THE 24 BITS AFTER THE LEADING 1.xxxx
    prepmul PREP( a <: a, b <: b, productsign :> productsign, productexp :> productexp, normalfraction :> normalfraction );

    // CLASSIFY THE INPUTS AND FLAG INFINITY, NAN, ZERO AND INVALID ( INF x ZERO )
    uint1   ZERO <:: (classA[0,1] | classB[0,1] );
    uint1   IF <:: ( classA[3,1] | classB[3,1] );
    uint1   NN <:: ( classA[2,1] | classA[1,1] | classB[2,1] | classB[1,1] );
    uint1   NV <:: IF & ZERO;
    uint1   OF = uninitialised;
    uint1   UF = uninitialised;

    flags := { IF, NN, NV, 1b0, OF, UF, 1b0 };
    while(1) {
        if( start ) {
            busy = 1;
            OF = 0; UF = 0;
            switch( { IF | NN, ZERO } ) {
                case 2b00: {
                    // STEPS: SETUP -> DOMUL -> NORMALISE -> ROUND -> ADJUSTEXP -> COMBINE
                    ++: // ALLOW 2 CYCLES TO PERFORM THE MULTIPLICATION, NORMALISATION AND ROUNDING
                    ++:
                    OF = cOF; UF = cUF; result = f32;
                }
                case 2b01: { result = { PREP.productsign, 31b0 }; }
                default: {
                    switch( { IF, ZERO } ) {
                        case 2b11: { result = 32hffc00000; }
                        case 2b10: { result = NN ? 32hffc00000 : { PREP.productsign, 31h7f800000 }; }
                        default: { result = 32hffc00000; }
                    }
                }
            }
            busy = 0;
        }
    }
}

// DIVIDE TWO FLOATING POINT NUMBERS
algorithm dofloatdivide(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint50  sigA,
    input   uint50  sigB,
    output  uint50  quotient
) <autorun> {
    uint50  remainder = uninitialised;
    uint50  temporary <:: { remainder[0,49], sigA[bit,1] };
    uint1   bitresult <:: __unsigned(temporary) >= __unsigned(sigB);
    uint2   normalshift <:: quotient[49,1] ? 2 : quotient[48,1];
    uint6   bit(63);

    busy := start | ( ~&bit ) | ( quotient[48,2] != 0 );
    always_after {
        // FIND QUOTIENT AND ENSURE 48 BIT FRACTION ( ie BITS 48 and 49 clear )
        if( start ) {
            bit = 49; quotient = 0; remainder = 0;
        } else {
            if( ~&bit ) {
                remainder = __unsigned(temporary) - ( bitresult ? __unsigned(sigB) : 0 );
                quotient[bit,1] = bitresult;
                bit = bit - 1;
            } else {
                quotient = quotient[ normalshift, 48 ];
            }
        }
    }
}
algorithm prepdivide(
    input   uint32  a,
    input   uint32  b,
    output  uint1   quotientsign,
    output  int10   quotientexp,
    output  uint50  sigA,
    output  uint50  sigB
) <autorun> {
    // BREAK DOWN INITIAL float32 INPUTS AND FIND SIGN OF RESULT AND EXPONENT OF QUOTIENT ( -1 IF DIVISOR > DIVIDEND )
    // ALIGN DIVIDEND TO THE LEFT, DIVISOR TO THE RIGHT
    uint1   AvB <:: ( fp32(b).fraction > fp32(a).fraction );
    always_after {
        quotientsign = fp32( a ).sign ^ fp32( b ).sign;
        quotientexp = fp32( a ).exponent - fp32( b ).exponent - AvB;
        sigA = { 1b1, fp32(a).fraction, 26b0 };
        sigB = { 27b1, fp32(b).fraction };
    }
}

algorithm floatdivide(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint32  a,
    input   uint32  b,
    input   uint4   classA,
    input   uint4   classB,
    output  uint1   quotientsign,
    output  int10   quotientexp,
    output  uint48  tonormalisebitstream,
    input   uint1   cOF,
    input   uint1   cUF,
    input   uint32  f32,
    output  uint7   flags,
    output  uint32  result
) <autorun,reginputs> {
    // CLASSIFY THE INPUTS AND FLAG INFINITY, NAN, ZERO AND DIVIDE ZERO
    uint1   IF <:: ( classA[3,1] | classB[3,1] );
    uint1   NN <:: ( classA[2,1] | classA[1,1] | classB[2,1] | classB[1,1] );
    uint1   NV = uninitialised;
    uint1   OF = uninitialised;
    uint1   UF = uninitialised;

    // PREPARE THE DIVISION, DO THE DIVISION, NORMALISE THE RESULT
    prepdivide PREP( a <: a, b <: b, quotientsign :> quotientsign, quotientexp :> quotientexp );
    dofloatdivide DODIVIDE( sigA <: PREP.sigA, sigB <: PREP.sigB, quotient :> tonormalisebitstream );

    DODIVIDE.start := 0; flags := { IF, NN, 1b0, classB[0,1], OF, UF, 1b0};
    while(1) {
        if( start ) {
            busy = 1;
            OF = 0; UF = 0;
            switch( { IF | NN,classA[0,1] | classB[0,1] } ) {
                case 2b00: {
                    DODIVIDE.start = 1; while( DODIVIDE.busy ) {}
                    OF = cOF; UF = cUF; result = f32;
                }
                case 2b01: { result = (classA[0,1] & classB[0,1] ) ? 32hffc00000 : { PREP.quotientsign, classB[0,1] ? 31h7f800000 : 31h0 }; }
                default: { result = ( classA[3,1] & classB[3,1] ) | NN | classB[0,1] ? 32hffc00000 : { PREP.quotientsign, (classA[0,1] | classB[3,1] ) ? 31b0 : 31h7f800000 }; }
            }
            busy = 0;
        }
    }
}

// ADAPTED FROM https://projectf.io/posts/square-root-in-verilog/
//
// MIT License
//
// Copyright (c) 2021 Will Green, Project F
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//
algorithm dofloatsqrt(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint50  start_ac,
    input   uint48  start_x,
    output  uint48  squareroot
) <autorun> {
    uint50  test_res <:: ac - { squareroot, 2b01 };
    uint50  ac = uninitialised;
    uint48  x = uninitialised;
    uint6   i(47);

    busy := start | ( i != 47 );
    always_after {
        if( start ) {
            i = 0; squareroot = 0; ac = start_ac; x = start_x;
        } else {
            if( i != 47 ) {
                ac = { test_res[49,1] ? ac[0,47] : test_res[0,47], x[46,2] };
                squareroot = { squareroot[0,47], ~test_res[49,1] };
                x = { x[0,46], 2b00 };
                i = i + 1;
            }
        }
    }
}
algorithm prepsqrt(
    input   uint32  a,
    output  uint50  start_ac,
    output  uint48  start_x,
    output  int10   squarerootexp
) <autorun> {
    // EXPONENT OF INPUT ( used to determine if 1x.xxxxx or 01.xxxxx for fixed point fraction to sqrt )
    // SQUARE ROOT EXPONENT IS HALF OF INPUT EXPONENT
    int10   exp  <:: fp32( a ).exponent - 127;
    always_after {
        start_ac = exp[0,1] ? { 48b0, 1b1, a[22,1] } : 1;
        start_x = exp[0,1] ? { a[0,22], 26b0 } : { fp32( a ).fraction, 25b0 };
        squarerootexp = ( exp >>> 1 );
    }
}

algorithm floatsqrt(
    input   uint1   start,
    output  uint1   busy(0),
    input   uint32  a,
    input   uint4   classA,
    output  int10   squarerootexp,
    output  uint24  normalfraction,
    input   uint1   cOF,
    input   uint1   cUF,
    input   uint32  f32,
    output  uint7   flags,
    output  uint32  result
) <autorun,reginputs> {
    // CLASSIFY THE INPUTS AND FLAG INFINITY, NAN, ZERO AND NOT VALID
    uint1   NN <:: classA[2,1] | classA[1,1];
    uint1   NV <:: classA[3,1] | NN | fp32( a ).sign;
    uint1   OF = uninitialised;
    uint1   UF = uninitialised;

    // PREPARE AND PERFORM THE SQUAREROOT, FAST NORMALISE THE RESULT
    prepsqrt PREP( a <: a, squarerootexp :> squarerootexp );
    dofloatsqrt DOSQRT( start_ac <: PREP.start_ac, start_x <: PREP.start_x );
    fastnormal24 NORMAL( tonormal <: DOSQRT.squareroot, normalfraction :> normalfraction );

    DOSQRT.start := 0; flags := { classA[3,1], NN, NV, 1b0, OF, UF, 1b0 };
    while(1) {
        if( start ) {
            busy = 1;
            OF = 0; UF = 0;
            switch( { classA[3,1] | NN,classA[0,1] | fp32( a ).sign } ) {
                case 2b00: {
                    // STEPS: SETUP -> DOSQRT -> NORMALISE -> ROUND -> ADJUSTEXP -> COMBINE
                    DOSQRT.start = 1; while( DOSQRT.busy ) {}
                    OF = cOF; UF = cUF; result = f32;
                }
                // DETECT sNAN, qNAN, -INF, -x -> qNAN AND  INF -> INF, 0 -> 0
                default: { result = fp32( a ).sign ? 32hffc00000 : a; }
            }
            busy = 0;
        }
    }
}

// FLOATING POINT COMPARISONS - ADAPTED FROM SOFT-FLOAT

/*============================================================================

License for Berkeley SoftFloat Release 3e

John R. Hauser
2018 January 20

The following applies to the whole of SoftFloat Release 3e as well as to
each source file individually.

Copyright 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018 The Regents of the
University of California.  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice,
    this list of conditions, and the following disclaimer.

 2. Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions, and the following disclaimer in the
    documentation and/or other materials provided with the distribution.

 3. Neither the name of the University nor the names of its contributors
    may be used to endorse or promote products derived from this software
    without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS "AS IS", AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE
DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

=============================================================================*/

algorithm floatcompare(
    input   uint32  a,
    input   uint32  b,
    input   uint4   classA,
    input   uint4   classB,
    output  uint7   flags,
    output  uint1   less,
    output  uint1   equal
) <autorun,reginputs> {
    uint1   INF <:: classA[3,1] | classB[3,1];
    uint1   NAN <:: classA[2,1] | classB[2,1] | classA[1,1] | classB[1,1];

    uint1   aequalb <:: ( a == b );                 uint1   aorbleft1equal0 <:: ~|( ( a | b ) << 1 );
    uint1   avb <:: ( a < b );

    // IDENTIFY NaN, RETURN 0 IF NAN, OTHERWISE RESULT OF COMPARISONS
    always_after {
        flags = { INF, {2{NAN}}, 4b0000 };
        less = ~NAN & ( ( fp32( a ).sign ^ fp32( b ).sign ) ? fp32( a ).sign & ~aorbleft1equal0 : ~aequalb & ( fp32( a ).sign ^ avb ) );
        equal = ~NAN & ( aequalb | aorbleft1equal0 );
    }
}
