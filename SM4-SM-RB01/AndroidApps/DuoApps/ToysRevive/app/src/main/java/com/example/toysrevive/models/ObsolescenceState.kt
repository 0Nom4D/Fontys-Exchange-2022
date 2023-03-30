package com.example.toysrevive.models

enum class ObsolescenceState {
    NO_STATE,
    BRAND_NEW,
    USED_BUT_NEW,
    USED,
    BAD,
    VERY_BAD,
}

val obsolescenceCorres = listOf(
    "Choose the obsolescence state of your toy",
    "Brand new",
    "Used but seems new",
    "Used",
    "Bad state",
    "Very bad state"
)
