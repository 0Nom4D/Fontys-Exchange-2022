package com.example.hapticfeedbacktechcase.ui.theme

import androidx.compose.ui.text.font.Font
import androidx.compose.ui.text.font.FontFamily
import androidx.compose.ui.text.font.FontStyle
import androidx.compose.ui.text.font.FontWeight

import com.example.hapticfeedbacktechcase.R

fun getPoppins(): FontFamily {
    return FontFamily(
        Font(R.font.poppins_light, FontWeight.Light),
        Font(R.font.poppins_black, FontWeight.Black),
        Font(R.font.poppins_bold, FontWeight.Bold),
        Font(R.font.poppins_blackitalic, FontWeight.Black, FontStyle.Italic),
        Font(R.font.poppins_italic, FontWeight.Normal, FontStyle.Italic),
        Font(R.font.poppins_regular, FontWeight.Normal),
        Font(R.font.poppins_thin, FontWeight.Thin),
        Font(R.font.poppins_thinitalic, FontWeight.Thin, FontStyle.Italic),
        Font(R.font.poppins_medium, FontWeight.Medium),
    )
}
