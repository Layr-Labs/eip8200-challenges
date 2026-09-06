import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copy `k` starts
at instruction index `1850 + 17 * k` and at byte `3032 + 20 * k`; the entry
`JUMPDEST`, the `base - 1` it derives and the closing jump sit on either side
of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem pc1846 : Artifact.submissionArtifact.instructionPC 1846 = 3027 := by rfl
@[simp] theorem pc1847 : Artifact.submissionArtifact.instructionPC 1847 = 3028 := by rfl
@[simp] theorem pc1848 : Artifact.submissionArtifact.instructionPC 1848 = 3030 := by rfl
@[simp] theorem pc1849 : Artifact.submissionArtifact.instructionPC 1849 = 3031 := by rfl
@[simp] theorem pc1850 : Artifact.submissionArtifact.instructionPC 1850 = 3032 := by rfl
@[simp] theorem pc1851 : Artifact.submissionArtifact.instructionPC 1851 = 3033 := by rfl
@[simp] theorem pc1852 : Artifact.submissionArtifact.instructionPC 1852 = 3035 := by rfl
@[simp] theorem pc1853 : Artifact.submissionArtifact.instructionPC 1853 = 3036 := by rfl
@[simp] theorem pc1854 : Artifact.submissionArtifact.instructionPC 1854 = 3038 := by rfl
@[simp] theorem pc1855 : Artifact.submissionArtifact.instructionPC 1855 = 3039 := by rfl
@[simp] theorem pc1856 : Artifact.submissionArtifact.instructionPC 1856 = 3040 := by rfl
@[simp] theorem pc1857 : Artifact.submissionArtifact.instructionPC 1857 = 3041 := by rfl
@[simp] theorem pc1858 : Artifact.submissionArtifact.instructionPC 1858 = 3042 := by rfl
@[simp] theorem pc1859 : Artifact.submissionArtifact.instructionPC 1859 = 3044 := by rfl
@[simp] theorem pc1860 : Artifact.submissionArtifact.instructionPC 1860 = 3045 := by rfl
@[simp] theorem pc1861 : Artifact.submissionArtifact.instructionPC 1861 = 3046 := by rfl
@[simp] theorem pc1862 : Artifact.submissionArtifact.instructionPC 1862 = 3047 := by rfl
@[simp] theorem pc1863 : Artifact.submissionArtifact.instructionPC 1863 = 3048 := by rfl
@[simp] theorem pc1864 : Artifact.submissionArtifact.instructionPC 1864 = 3049 := by rfl
@[simp] theorem pc1865 : Artifact.submissionArtifact.instructionPC 1865 = 3050 := by rfl
@[simp] theorem pc1866 : Artifact.submissionArtifact.instructionPC 1866 = 3051 := by rfl
@[simp] theorem pc1867 : Artifact.submissionArtifact.instructionPC 1867 = 3052 := by rfl
@[simp] theorem pc1868 : Artifact.submissionArtifact.instructionPC 1868 = 3053 := by rfl
@[simp] theorem pc1869 : Artifact.submissionArtifact.instructionPC 1869 = 3055 := by rfl
@[simp] theorem pc1870 : Artifact.submissionArtifact.instructionPC 1870 = 3056 := by rfl
@[simp] theorem pc1871 : Artifact.submissionArtifact.instructionPC 1871 = 3058 := by rfl
@[simp] theorem pc1872 : Artifact.submissionArtifact.instructionPC 1872 = 3059 := by rfl
@[simp] theorem pc1873 : Artifact.submissionArtifact.instructionPC 1873 = 3060 := by rfl
@[simp] theorem pc1874 : Artifact.submissionArtifact.instructionPC 1874 = 3061 := by rfl
@[simp] theorem pc1875 : Artifact.submissionArtifact.instructionPC 1875 = 3062 := by rfl
@[simp] theorem pc1876 : Artifact.submissionArtifact.instructionPC 1876 = 3064 := by rfl
@[simp] theorem pc1877 : Artifact.submissionArtifact.instructionPC 1877 = 3065 := by rfl
@[simp] theorem pc1878 : Artifact.submissionArtifact.instructionPC 1878 = 3066 := by rfl
@[simp] theorem pc1879 : Artifact.submissionArtifact.instructionPC 1879 = 3067 := by rfl
@[simp] theorem pc1880 : Artifact.submissionArtifact.instructionPC 1880 = 3068 := by rfl
@[simp] theorem pc1881 : Artifact.submissionArtifact.instructionPC 1881 = 3069 := by rfl
@[simp] theorem pc1882 : Artifact.submissionArtifact.instructionPC 1882 = 3070 := by rfl
@[simp] theorem pc1883 : Artifact.submissionArtifact.instructionPC 1883 = 3071 := by rfl
@[simp] theorem pc1884 : Artifact.submissionArtifact.instructionPC 1884 = 3072 := by rfl
@[simp] theorem pc1885 : Artifact.submissionArtifact.instructionPC 1885 = 3073 := by rfl
@[simp] theorem pc1886 : Artifact.submissionArtifact.instructionPC 1886 = 3075 := by rfl
@[simp] theorem pc1887 : Artifact.submissionArtifact.instructionPC 1887 = 3076 := by rfl
@[simp] theorem pc1888 : Artifact.submissionArtifact.instructionPC 1888 = 3078 := by rfl
@[simp] theorem pc1889 : Artifact.submissionArtifact.instructionPC 1889 = 3079 := by rfl
@[simp] theorem pc1890 : Artifact.submissionArtifact.instructionPC 1890 = 3080 := by rfl
@[simp] theorem pc1891 : Artifact.submissionArtifact.instructionPC 1891 = 3081 := by rfl
@[simp] theorem pc1892 : Artifact.submissionArtifact.instructionPC 1892 = 3082 := by rfl
@[simp] theorem pc1893 : Artifact.submissionArtifact.instructionPC 1893 = 3084 := by rfl
@[simp] theorem pc1894 : Artifact.submissionArtifact.instructionPC 1894 = 3085 := by rfl
@[simp] theorem pc1895 : Artifact.submissionArtifact.instructionPC 1895 = 3086 := by rfl
@[simp] theorem pc1896 : Artifact.submissionArtifact.instructionPC 1896 = 3087 := by rfl
@[simp] theorem pc1897 : Artifact.submissionArtifact.instructionPC 1897 = 3088 := by rfl
@[simp] theorem pc1898 : Artifact.submissionArtifact.instructionPC 1898 = 3089 := by rfl
@[simp] theorem pc1899 : Artifact.submissionArtifact.instructionPC 1899 = 3090 := by rfl
@[simp] theorem pc1900 : Artifact.submissionArtifact.instructionPC 1900 = 3091 := by rfl
@[simp] theorem pc1901 : Artifact.submissionArtifact.instructionPC 1901 = 3092 := by rfl
@[simp] theorem pc1902 : Artifact.submissionArtifact.instructionPC 1902 = 3093 := by rfl
@[simp] theorem pc1903 : Artifact.submissionArtifact.instructionPC 1903 = 3095 := by rfl
@[simp] theorem pc1904 : Artifact.submissionArtifact.instructionPC 1904 = 3096 := by rfl
@[simp] theorem pc1905 : Artifact.submissionArtifact.instructionPC 1905 = 3098 := by rfl
@[simp] theorem pc1906 : Artifact.submissionArtifact.instructionPC 1906 = 3099 := by rfl
@[simp] theorem pc1907 : Artifact.submissionArtifact.instructionPC 1907 = 3100 := by rfl
@[simp] theorem pc1908 : Artifact.submissionArtifact.instructionPC 1908 = 3101 := by rfl
@[simp] theorem pc1909 : Artifact.submissionArtifact.instructionPC 1909 = 3102 := by rfl
@[simp] theorem pc1910 : Artifact.submissionArtifact.instructionPC 1910 = 3104 := by rfl
@[simp] theorem pc1911 : Artifact.submissionArtifact.instructionPC 1911 = 3105 := by rfl
@[simp] theorem pc1912 : Artifact.submissionArtifact.instructionPC 1912 = 3106 := by rfl
@[simp] theorem pc1913 : Artifact.submissionArtifact.instructionPC 1913 = 3107 := by rfl
@[simp] theorem pc1914 : Artifact.submissionArtifact.instructionPC 1914 = 3108 := by rfl
@[simp] theorem pc1915 : Artifact.submissionArtifact.instructionPC 1915 = 3109 := by rfl
@[simp] theorem pc1916 : Artifact.submissionArtifact.instructionPC 1916 = 3110 := by rfl
@[simp] theorem pc1917 : Artifact.submissionArtifact.instructionPC 1917 = 3111 := by rfl
@[simp] theorem pc1918 : Artifact.submissionArtifact.instructionPC 1918 = 3112 := by rfl
@[simp] theorem pc1919 : Artifact.submissionArtifact.instructionPC 1919 = 3113 := by rfl
@[simp] theorem pc1920 : Artifact.submissionArtifact.instructionPC 1920 = 3115 := by rfl
@[simp] theorem pc1921 : Artifact.submissionArtifact.instructionPC 1921 = 3116 := by rfl
@[simp] theorem pc1922 : Artifact.submissionArtifact.instructionPC 1922 = 3118 := by rfl
@[simp] theorem pc1923 : Artifact.submissionArtifact.instructionPC 1923 = 3119 := by rfl
@[simp] theorem pc1924 : Artifact.submissionArtifact.instructionPC 1924 = 3120 := by rfl
@[simp] theorem pc1925 : Artifact.submissionArtifact.instructionPC 1925 = 3121 := by rfl
@[simp] theorem pc1926 : Artifact.submissionArtifact.instructionPC 1926 = 3122 := by rfl
@[simp] theorem pc1927 : Artifact.submissionArtifact.instructionPC 1927 = 3124 := by rfl
@[simp] theorem pc1928 : Artifact.submissionArtifact.instructionPC 1928 = 3125 := by rfl
@[simp] theorem pc1929 : Artifact.submissionArtifact.instructionPC 1929 = 3126 := by rfl
@[simp] theorem pc1930 : Artifact.submissionArtifact.instructionPC 1930 = 3127 := by rfl
@[simp] theorem pc1931 : Artifact.submissionArtifact.instructionPC 1931 = 3128 := by rfl
@[simp] theorem pc1932 : Artifact.submissionArtifact.instructionPC 1932 = 3129 := by rfl
@[simp] theorem pc1933 : Artifact.submissionArtifact.instructionPC 1933 = 3130 := by rfl
@[simp] theorem pc1934 : Artifact.submissionArtifact.instructionPC 1934 = 3131 := by rfl
@[simp] theorem pc1935 : Artifact.submissionArtifact.instructionPC 1935 = 3132 := by rfl
@[simp] theorem pc1936 : Artifact.submissionArtifact.instructionPC 1936 = 3133 := by rfl
@[simp] theorem pc1937 : Artifact.submissionArtifact.instructionPC 1937 = 3135 := by rfl
@[simp] theorem pc1938 : Artifact.submissionArtifact.instructionPC 1938 = 3136 := by rfl
@[simp] theorem pc1939 : Artifact.submissionArtifact.instructionPC 1939 = 3138 := by rfl
@[simp] theorem pc1940 : Artifact.submissionArtifact.instructionPC 1940 = 3139 := by rfl
@[simp] theorem pc1941 : Artifact.submissionArtifact.instructionPC 1941 = 3140 := by rfl
@[simp] theorem pc1942 : Artifact.submissionArtifact.instructionPC 1942 = 3141 := by rfl
@[simp] theorem pc1943 : Artifact.submissionArtifact.instructionPC 1943 = 3142 := by rfl
@[simp] theorem pc1944 : Artifact.submissionArtifact.instructionPC 1944 = 3144 := by rfl
@[simp] theorem pc1945 : Artifact.submissionArtifact.instructionPC 1945 = 3145 := by rfl
@[simp] theorem pc1946 : Artifact.submissionArtifact.instructionPC 1946 = 3146 := by rfl
@[simp] theorem pc1947 : Artifact.submissionArtifact.instructionPC 1947 = 3147 := by rfl
@[simp] theorem pc1948 : Artifact.submissionArtifact.instructionPC 1948 = 3148 := by rfl
@[simp] theorem pc1949 : Artifact.submissionArtifact.instructionPC 1949 = 3149 := by rfl
@[simp] theorem pc1950 : Artifact.submissionArtifact.instructionPC 1950 = 3150 := by rfl
@[simp] theorem pc1951 : Artifact.submissionArtifact.instructionPC 1951 = 3151 := by rfl
@[simp] theorem pc1952 : Artifact.submissionArtifact.instructionPC 1952 = 3152 := by rfl
@[simp] theorem pc1953 : Artifact.submissionArtifact.instructionPC 1953 = 3153 := by rfl
@[simp] theorem pc1954 : Artifact.submissionArtifact.instructionPC 1954 = 3155 := by rfl
@[simp] theorem pc1955 : Artifact.submissionArtifact.instructionPC 1955 = 3156 := by rfl
@[simp] theorem pc1956 : Artifact.submissionArtifact.instructionPC 1956 = 3158 := by rfl
@[simp] theorem pc1957 : Artifact.submissionArtifact.instructionPC 1957 = 3159 := by rfl
@[simp] theorem pc1958 : Artifact.submissionArtifact.instructionPC 1958 = 3160 := by rfl
@[simp] theorem pc1959 : Artifact.submissionArtifact.instructionPC 1959 = 3161 := by rfl
@[simp] theorem pc1960 : Artifact.submissionArtifact.instructionPC 1960 = 3162 := by rfl
@[simp] theorem pc1961 : Artifact.submissionArtifact.instructionPC 1961 = 3164 := by rfl
@[simp] theorem pc1962 : Artifact.submissionArtifact.instructionPC 1962 = 3165 := by rfl
@[simp] theorem pc1963 : Artifact.submissionArtifact.instructionPC 1963 = 3166 := by rfl
@[simp] theorem pc1964 : Artifact.submissionArtifact.instructionPC 1964 = 3167 := by rfl
@[simp] theorem pc1965 : Artifact.submissionArtifact.instructionPC 1965 = 3168 := by rfl
@[simp] theorem pc1966 : Artifact.submissionArtifact.instructionPC 1966 = 3169 := by rfl
@[simp] theorem pc1967 : Artifact.submissionArtifact.instructionPC 1967 = 3170 := by rfl
@[simp] theorem pc1968 : Artifact.submissionArtifact.instructionPC 1968 = 3171 := by rfl
@[simp] theorem pc1969 : Artifact.submissionArtifact.instructionPC 1969 = 3172 := by rfl
@[simp] theorem pc1970 : Artifact.submissionArtifact.instructionPC 1970 = 3173 := by rfl
@[simp] theorem pc1971 : Artifact.submissionArtifact.instructionPC 1971 = 3175 := by rfl
@[simp] theorem pc1972 : Artifact.submissionArtifact.instructionPC 1972 = 3176 := by rfl
@[simp] theorem pc1973 : Artifact.submissionArtifact.instructionPC 1973 = 3178 := by rfl
@[simp] theorem pc1974 : Artifact.submissionArtifact.instructionPC 1974 = 3179 := by rfl
@[simp] theorem pc1975 : Artifact.submissionArtifact.instructionPC 1975 = 3180 := by rfl
@[simp] theorem pc1976 : Artifact.submissionArtifact.instructionPC 1976 = 3181 := by rfl
@[simp] theorem pc1977 : Artifact.submissionArtifact.instructionPC 1977 = 3182 := by rfl
@[simp] theorem pc1978 : Artifact.submissionArtifact.instructionPC 1978 = 3184 := by rfl
@[simp] theorem pc1979 : Artifact.submissionArtifact.instructionPC 1979 = 3185 := by rfl
@[simp] theorem pc1980 : Artifact.submissionArtifact.instructionPC 1980 = 3186 := by rfl
@[simp] theorem pc1981 : Artifact.submissionArtifact.instructionPC 1981 = 3187 := by rfl
@[simp] theorem pc1982 : Artifact.submissionArtifact.instructionPC 1982 = 3188 := by rfl
@[simp] theorem pc1983 : Artifact.submissionArtifact.instructionPC 1983 = 3189 := by rfl
@[simp] theorem pc1984 : Artifact.submissionArtifact.instructionPC 1984 = 3190 := by rfl
@[simp] theorem pc1985 : Artifact.submissionArtifact.instructionPC 1985 = 3191 := by rfl
@[simp] theorem pc1986 : Artifact.submissionArtifact.instructionPC 1986 = 3192 := by rfl
@[simp] theorem pc1987 : Artifact.submissionArtifact.instructionPC 1987 = 3193 := by rfl
@[simp] theorem pc1988 : Artifact.submissionArtifact.instructionPC 1988 = 3196 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
