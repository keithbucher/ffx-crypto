"""
__author__ Keith Bucher (keith.bucher+code@gmail.com)
Module that implements FFX encryption as specified in NIST draft SP800-38G
"""

import string
import math
import binascii
import functools

import gmpy2
from gmpy2 import mpfr
from gmpy2 import mpz

from Crypto.Cipher import AES
from Crypto.Util import Counter
from builtins import int
from binascii import unhexlify, hexlify

from abc import ABCMeta, abstractmethod
from test.pickletester import metaclass

# Credit to Tripp Lilley from StackOverflow for this function,
# modified to pad if necessary and handle zero values properly
def long_to_bytes (val, iBlocksize=1, endianness='big'):
    """
    Use :ref:`string formatting` and :func:`~binascii.unhexlify` to
    convert ``val``, a :func:`long`, to a byte :func:`str`.

    :param long val: The value to pack

    :param int iBlockSize: If specified, output will be right-justified and padded with zeroes

    :param str endianness: The endianness of the result. ``'big'`` for
      big-endian, ``'little'`` for little-endian.

    If you want byte- and word-ordering to differ, you're on your own.

    Using :ref:`string formatting` lets us use Python's C innards.
    """

    # one (1) hex digit per four (4) bits
    width = val.bit_length()

    # Account for zero values
    if(width == 0): width = 8

    # unhexlify wants an even multiple of eight (8) bits, but we don't
    # want more digits than we need (hence the ternary-ish 'or')
    width += 8 - ((width % 8) or 8)

    # format width specifier: four (4) bits per hex digit
    fmt = '%%0%dx' % (width // 4)

    # prepend zero (0) to the width, to zero-pad the output
    s = bytearray(unhexlify(fmt % val))

    if endianness == 'little':
        # see http://stackoverflow.com/a/931095/309233
        s = s[::-1]

    # Pad output if necessary
    sPad = bytearray()
    if(iBlocksize > 1 and ((len(s) % iBlocksize) != 0)):
        sPad = bytearray(b'\x00' * (iBlocksize - (len(s) % iBlocksize)) )

    sPad.extend(s)

    return sPad

def bytes_to_long(bytestring):
    """Given a ``bytestring`` returns its integer representation ``N``.
    """

    N = binascii.hexlify(bytestring)
    N = mpz(N, 16)

    return N


class UnsupportedTypeException(Exception):
    """
    Unsupported type used in function
    """
    pass

class InvalidRadixException(Exception):
    """
    Invalid radix values passed, can occur when trying to combine FFXStrings with different radix
    """
    pass

class InvalidTweakLengthException(Exception):
    """
    Invalid length for tweak specified.  For FFX mode FF3, the tweak must be exactly 64 characters long.
    """
    pass


class InvalidFFXModeException(Exception):
    """
    Invalid FFX mode specified.  Valid modes are FFXCrypt.MODE_FF1, FFXCrypt.MODE_FF2, FFXCrypt.MODE_FF3
    """
    pass


class FFXString(object):
    """
    Represents a character string that FFX will operate on
    """
    def __init__(self, sInit, iRadix=10, iBlockSize=128):
        """
        Construct a new FFX character string

        :param    sInit        The value of the character string, can be int, str or FFXString
        :param    iRadix        The radix of the character string alphabet, default 10 for integers
        :param    iBlockSize    The blocksize to use with the character string in bits, default 128 bits
        :return    returns nothing
        """

        # Determine the type of the initial value
        if(isinstance(sInit, int)):
            self._sValue = mpz(sInit).digits(iRadix)
        elif(isinstance(sInit, str)):
            self._sValue = sInit
        elif(isinstance(sInit, FFXString)):
            self._sValue = sInit._sValue
        elif(isinstance(sInit, bytearray)):
            self._sValue = mpz(bytes_to_long(sInit)).digits(iRadix)
        else:
            raise UnsupportedTypeException(type(sInit))

        self._iRadix = iRadix
        self._iBlockSize = iBlockSize
        self._iLen = len(self._sValue)

        # Representations of value as integer and bytearray
        self._iValue = None
        self._bValue = None

    def __add__(self, other):
        retval = self._sValue
        if isinstance(other, FFXString):
            if(self._iRadix != other._iRadix):
                raise InvalidRadixException
            retval += other._sValue
        return retval


    def __getitem__( self, key ) :
        if isinstance( key, slice ) :
            #Get the start, stop, and step from the slice
            retval = ''
            for ii in range(*key.indices(len(self))):
                retval += self._sValue[ii]
            return FFXString(retval, self._iRadix, self._iBlockSize)
            #return [self[ii] for ii in range(*key.indices(len(self)))]
        elif isinstance( key, int ) :
            if key < 0 : #Handle negative indices
                key += len( self )
            if key >= len( self ) :
                raise IndexError
            return self._sValue[key]
        else:
            raise TypeError

    def __len__(self):
        if self._iLen == None:
            self._iLen = len(self._sValue)
        return self._iLen

    def __str__(self):
        return self._sValue

    def getMid(self, iMode):
        """
        Return the middle index to use when splitting the string
        """
        if(iMode == FFXCrypt.MODE_FF3):
            retval = int(math.ceil((self._iLen * 1.0) / 2))
        else:
            retval = int(math.floor((self._iLen * 1.0) / 2))

        return retval

    def to_int(self):
        if not self._iValue:
            self._iValue = int(self._sValue, self._iRadix)
        return self._iValue

    def to_bytes(self, iBlocksize=1):
        """
        Return bytearray that represents big-endian encoded integer value of _sValue
        """
        #if not self._bValue:
        self._bValue = long_to_bytes(self.to_int(), iBlocksize=iBlocksize)
        return(self._bValue)


class FFXMode(metaclass=ABCMeta):
    """
    Abstract Class that represents FFX cryptographic modes
    """

    _iRnds = 0

    @abstractmethod
    def encrypt(self, sData, sTweak=None):
        pass

    @abstractmethod
    def decrypt(self, sData, sTweak=None):
        pass

    @abstractmethod
    def crypt(self, iDirection, sData, sTweak=None):
        pass

class FFXModeFF1(FFXMode):

    def __init__(self, ffxKey, iRadix=10, iBlockSize=128):
        """
        Contruct a new FFX FF1 mode cryptographic object

        :param    ffxKey          The key to use in cryptographic operations, should be FFXstring object
        :param    iRadix        The radix of the character sting alphabet, default 10 for integers
        :param    iBlockSize    The blocksize to use with the character string in bits, default 128 bits
        """

        self._ffxKey = None

        self._iRadix = iRadix
        self._iBlockSize = iBlockSize
        if(isinstance(ffxKey, FFXString)):
            self._ffxKey = ffxKey
        else:
            raise UnsupportedTypeException(type(ffxKey))

        self._iRnds = 10

    def decrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self.crypt(FFXCrypt.FFX_DECRYPT, sData, sTweak))

    def encrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self.crypt(FFXCrypt.FFX_ENCRYPT, sData, sTweak))

    def crypt(self, iDirection, sData, sTweak=None):
        # TODO: type checking

        # Note, used variable notation from NIST 800-38g draft

        # Set rounds
        if(sTweak != None):
            t = len(sTweak)
        else:
            t = 0

        # Split data into substrings, FF1 steps 1 & 2
        n = len(sData)
        u = sData.getMid(FFXCrypt.MODE_FF1)
        v = n-u


        A = sData[:u]
        B = sData[u:]

        #print("A = " + str(A))
        #print("B = " + str(B))

        #print("A+B = " + str(A + B))

        # Calculate byte lengths, FF1 step 3
        b = math.ceil(math.ceil(v*math.log(self._iRadix, 2))/8.0)
        d = 4*math.ceil(b/4)+4

        # Calculate initial block P, FF1 step 4
        P = bytearray(b"\x01\x02\x01")
        P.extend( long_to_bytes(self._iRadix, iBlocksize=3))
        P.extend(b"\x0a")
        P.extend( long_to_bytes(u % 256))
        P.extend( long_to_bytes(n, iBlocksize=4))
        P.extend( long_to_bytes(t, iBlocksize=4))

        # Execute Feistel rounds, FF1 step 5
        if(iDirection == FFXCrypt.FFX_ENCRYPT):
            iStart = 0
            iEnd = self._iRnds
            iMult = 1
        elif(iDirection == FFXCrypt.FFX_DECRYPT):
            iStart = self._iRnds
            iEnd = 0
            iMult = -1

        for i in range(iStart, iEnd):
            Q = bytearray(b'')
            # FF1 5.i
            if(sTweak != None):
                Q.extend(str(sTweak).encode())
            Q.extend(b'\x00' * ((-t-b-1) % 16))
            Q.extend(long_to_bytes(i))
            Q.extend(B.to_bytes(b))

            # FF1 5.ii
            bKey = bytes(self._ffxKey.to_bytes(16))
            #bKey = bytes(b'\x00'*16)
            #print(binascii.hexlify(bKey))
            #print(len(self._ffxKey.to_bytes(16)))
            cbcAES = AES.new(bKey, AES.MODE_CBC, '\x00' * AES.block_size)
            sPlainText = bytearray()
            sPlainText.extend(P)
            sPlainText.extend(Q)
            R = cbcAES.encrypt(bytes(sPlainText))[-16:]

            # FF1 5.iii
            ebcAES = AES.new(bKey, AES.MODE_ECB)
            sTmp = bytearray(R)
            for j in range(1, math.ceil(d/16.0)):
                sBlockPlaintext = bytearray(R[x] ^ j.to_bytes(16)[x] for x in range(16))
                sBlock = ebcAES.encrypt(sBlockPlaintext)
                sTmp.extend(sBlock)

            S = bytearray(R[:d])

            # FF1 5.iv
            y = FFXString(S, iRadix=2).to_int()

            # FF1 5.v
            if( i % 2 == 0):
                m = u
            else:
                m = v

            # FF1 5.vi
            c = (A.to_int() + iMult*y) % (self._iRadix ** m)
            # FF1 5.vii
            strTmp = str(FFXString(c, iRadix=self._iRadix))
            C = FFXString(strTmp[:m], iRadix=self._iRadix)

            # FF1 5.viii
            A = B

            # FF1 5.ix
            B = C

        # FF1 6
        sRetValue = str(A).rjust(u, '0') + str(B).rjust(v, '0')
        return(sRetValue)

class FFXModeFF2(FFXMode):

    def __init__(self, ffxKey, iRadix=10, iBlockSize=128):
        """
        Contruct a new FFX FF2 mode cryptographic object

        :param    ffxKey          The key to use in cryptographic operations, should be FFXstring object
        :param    iRadix        The radix of the character sting alphabet, default 10 for integers
        :param    iBlockSize    The blocksize to use with the character string in bits, default 128 bits
        """

        self._ffxKey = None

        self._iRadix = iRadix
        self._iBlockSize = iBlockSize
        if(isinstance(ffxKey, FFXString)):
            self._ffxKey = ffxKey
        else:
            raise UnsupportedTypeException(type(ffxKey))

        self._iRnds = 10

    def decrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self.crypt(FFXCrypt.FFX_DECRYPT, sData, sTweak))

    def encrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self.crypt(FFXCrypt.FFX_ENCRYPT, sData, sTweak))

    def crypt(self, iDirection, sData, sTweak=None):
        # TODO: type checking

        # Note, used variable notation from NIST 800-38g draft

        # Set rounds
        if(sTweak != None):
            t = len(sTweak)
        else:
            t = 0

        # Split data into substrings, FF2 steps 1 & 2
        n = len(sData)
        u = sData.getMid(FFXCrypt.MODE_FF2)
        v = n-u


        A = sData[:u]
        B = sData[u:]

        #print("A = " + str(A))
        #print("B = " + str(B))

        #print("A+B = " + str(A + B))

        # Calculate byte lengths, FF1 step 3
        #b = math.ceil(math.ceil(v*math.log(self._iRadix, 2))/8.0)
        #d = 4*math.ceil(b/4)+4

        # FF2 step 3
        P = bytearray(b'')
        P.extend(long_to_bytes(self._iRadix, iBlocksize=1))
        if(t > 0):
            P.extend(long_to_bytes(t, iBlocksize=1))
            P.extend(long_to_bytes(n, iBlocksize=1))
            P.extend(sTweak.to_bytes(iBlocksize=13))
        else:
            P.extend(b'\x00')
            P.extend(long_to_bytes(n, iBlocksize=1))
            P.extend(b'\x00'*13)

        # FF2 step 4
        bKeyK = bytes(self._ffxKey.to_bytes(16))
        ebcAES_K = AES.new(bKeyK, AES.MODE_ECB)
        J = ebcAES_K.encrypt(bytes(P))


        # Execute Feistel rounds, FF2 step 5
        if(iDirection == FFXCrypt.FFX_ENCRYPT):
            iStart = 0
            iEnd = self._iRnds
            iMult = 1
        elif(iDirection == FFXCrypt.FFX_DECRYPT):
            iStart = self._iRnds
            iEnd = 0
            iMult = -1

        for i in range(iStart, iEnd):
            Q = bytearray(b'')
            # FF2 5.i
            Q.extend(long_to_bytes(i, iBlocksize=1))
            Q.extend(B.to_bytes(15))

            # FF2 5.ii
            bKeyJ = bytes(J)
            ebcAES_J = AES.new(bKeyJ, AES.MODE_ECB)
            bTmp = ebcAES_J.encrypt(bytes(Q))
            Y = bytearray(bTmp)

            # FF2 5.iii
            y = FFXString(Y, iRadix=2).to_int()

            # FF2 5.iv
            if( i % 2 == 0):
                m = u
            else:
                m = v

            # FF2 5.v
            c = (A.to_int() + iMult*y) % (self._iRadix ** m)
            # FF2 5.vi
            strTmp = str(FFXString(c, iRadix=self._iRadix))
            C = FFXString(strTmp[:m], iRadix=self._iRadix)

            # FF2 5.vii
            A = B

            # FF2 5.viii
            B = C

        # FF2 6
        sRetValue = str(A).rjust(u, '0') + str(B).rjust(v, '0')
        return(sRetValue)

class FFXModeFF3(FFXMode):

    def __init__(self, ffxKey, iRadix=10, iBlockSize=128):
        """
        Contruct a new FFX FF2 mode cryptographic object

        :param    ffxKey          The key to use in cryptographic operations, should be FFXstring object
        :param    iRadix        The radix of the character sting alphabet, default 10 for integers
        :param    iBlockSize    The blocksize to use with the character string in bits, default 128 bits
        """

        self._ffxKey = None

        self._iRadix = iRadix
        self._iBlockSize = iBlockSize
        if(isinstance(ffxKey, FFXString)):
            self._ffxKey = ffxKey
        else:
            raise UnsupportedTypeException(type(ffxKey))

        self._iRnds = 8

    def decrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self.crypt(FFXCrypt.FFX_DECRYPT, sData, sTweak))

    def encrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self.crypt(FFXCrypt.FFX_ENCRYPT, sData, sTweak))

    def crypt(self, iDirection, sData, sTweak=None):
        # TODO: type checking

        # Note, used variable notation from NIST 800-38g draft

        # Set rounds
        if(sTweak != None):
            t = len(sTweak)
            # FF3 requires 64 bit tweak
            if(t != 8):
                raise InvalidTweakLengthException
        else:
            raise InvalidTweakLengthException

        # Split data into substrings, FF3 steps 1 & 2
        n = len(sData)
        u = sData.getMid(iMode=FFXCrypt.MODE_FF3)
        v = n-u


        A = sData[:u]
        B = sData[u:]

        # FF3 step 3
        TL = bytearray(str(sTweak[:4]).encode())
        TR = bytearray(str(sTweak[4:]).encode())

        # Execute Feistel rounds, FF3 step 4
        if(iDirection == FFXCrypt.FFX_ENCRYPT):
            iStart = 0
            iEnd = self._iRnds
            iMult = 1
        elif(iDirection == FFXCrypt.FFX_DECRYPT):
            iStart = self._iRnds
            iEnd = 0
            iMult = -1

        for i in range(iStart, iEnd):
            # FF3 5.i
            W = bytearray(b'')
            if( i % 2 == 0):
                m = u
                W.extend(TR)
            else:
                m = v
                W.extend(TL)

            # FF3 5.ii
            P = bytearray(b'')
            sTmp = B.to_bytes()
            sTmp.reverse()
            strTmp = FFXString(sTmp, iRadix=self._iRadix, iBlockSize=self._iBlockSize)
            P.extend(strTmp.to_bytes(iBlocksize=12))
            for x in range(4):
                bTmp = bytearray(W[x] ^ long_to_bytes(i, 4)[x])
                P.extend(long_to_bytes(bTmp[0]))
            P.reverse()

            # FF3 5.iii
            bKey = bytes(self._ffxKey.to_bytes(16))
            ebcAES = AES.new(bKey, AES.MODE_ECB)
            bTmp = ebcAES.encrypt(bytes(P))
            Y = bytearray(bTmp)

            # FF3 5.iv
            Y.reverse()
            y = FFXString(Y, iRadix=2).to_int()

            # FF3 5.v
            #sTmp = FFXString(A.to_bytes().reverse())
            sTmp = A.to_bytes()
            sTmp.reverse()
            strTmp = FFXString(sTmp, iRadix=self._iRadix, iBlockSize=self._iBlockSize)
            c = (strTmp.to_int() + iMult*y) % (self._iRadix ** m)

            # FF3 5.vi
            strTmp = str(FFXString(c, iRadix=self._iRadix, iBlockSize=self._iBlockSize))[::-1]

            C = FFXString(strTmp[:m], iRadix=self._iRadix, iBlockSize=self._iBlockSize)

            # FF3 5.vii
            A = B

            # FF3 5.viii
            B = C

        # FF3 5
        sRetValue = str(A).rjust(u, '0') + str(B).rjust(v, '0')
        return(sRetValue)


class FFXCrypt(object):
    """
    Class that handles FFX cryptographic operations on FFX character strings
    """

    FFX_ENCRYPT = 1
    FFX_DECRYPT = 2

    MODE_FF1 = 1
    MODE_FF2 = 2
    MODE_FF3 = 3

    def __init__(self, ffxKey, iMode=MODE_FF1, iRadix=10, iBlockSize=128):
        """
        Contruct a new FFX cryptographic object

        :param    ffxKey          The key to use in cryptographic operations, should be FFXstring object
        :param    iMode         The FFX mode to use, options are MODE_FF1 (default), MODE_FF2, MODE_FF3
        :param    iRadix        The radix of the character sting alphabet, default 10 for integers
        :param    iBlockSize    The blocksize to use with the character string in bits, default 128 bits
        """

        self._ffxKey = None

        self._iRadix = iRadix
        self._iBlockSize = iBlockSize
        if(isinstance(ffxKey, FFXString)):
            self._ffxKey = ffxKey
        else:
            raise UnsupportedTypeException(type(ffxKey))

        if(iMode == self.MODE_FF1):
            self._objMode = FFXModeFF1(ffxKey, iRadix, iBlockSize)
        elif(iMode == self.MODE_FF2):
            self._objMode = FFXModeFF2(ffxKey, iRadix, iBlockSize)
        elif(iMode == self.MODE_FF3):
            self._objMode = FFXModeFF3(ffxKey, iRadix, iBlockSize)
        else:
            raise InvalidFFXModeException


    def decrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self._objMode.crypt(self.FFX_DECRYPT, sData, sTweak))

    def encrypt(self, sData, sTweak=None):
        """
        Encrypt data

        :param    sTweak    The tweak to use
        :param    sData     The data to encrypt
        """

        # Call crypt function with encryption direction
        return(self._objMode.crypt(self.FFX_ENCRYPT, sData, sTweak))

    def _crypt(self, iDirection, sData, sTweak=None):
        # Call crypt function with encryption direction
        return(self._objMode.crypt(iDirection, sData, sTweak))





# Start test code
#sData = FFXString('123456789')
bKey = bytearray(unhexlify('2b7e151628aed2a6abf7158809cf4f3c'))

sKey = FFXString(bKey)

iRadix = 10
sData = FFXString('0123456789', iRadix=iRadix)
#sData = FFXString('0143456687', iRadix=iRadix)
#sTweak = FFXString('9876543210', iRadix=iRadix)
sTweak = FFXString('98765432', iRadix=iRadix)
#sTweak = None

"""
bVal = FFXString('78728').to_bytes(3)
print("bVal = ")
print(hexlify(bVal))
lVal = bytes_to_long(bVal)
print(lVal)
"""

sCrypt = FFXCrypt(sKey, iMode=FFXCrypt.MODE_FF3).encrypt(sData, sTweak)
print('sCrypt = ' + sCrypt)

sPlain = FFXCrypt(sKey, iMode=FFXCrypt.MODE_FF3).decrypt(sData, sTweak)
print('sPlain = ' + sPlain)




