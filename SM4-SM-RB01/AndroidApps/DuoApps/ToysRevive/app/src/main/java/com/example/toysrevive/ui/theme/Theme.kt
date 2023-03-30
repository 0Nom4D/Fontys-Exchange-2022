package com.example.toysrevive.ui.theme

import androidx.compose.foundation.isSystemInDarkTheme
import androidx.compose.material.MaterialTheme
import androidx.compose.material.darkColors
import androidx.compose.material.lightColors
import androidx.compose.runtime.Composable
import androidx.compose.ui.graphics.Color

private val DarkColorPalette = darkColors(
    primary = ReviveBlue500,
    primaryVariant = ReviveBlue700,
    secondary = ReviveOrange700,
    background = Color.Black,
    surface = Color(0xFFF7F8F8),
    onPrimary = Color.White,
    onSecondary = Color.Black,
    onBackground = Color.White,
    onSurface = Color.Black
)

private val LightColorPalette = lightColors(
    primary = ReviveBlue200,
    primaryVariant = ReviveBlue500,
    secondary = ReviveOrange500,
    background = Color.White,
    surface = Color(0xFFF7F8F8),
    onPrimary = Color.Black,
    onSecondary = Color.Black,
    onBackground = Color.Black,
    onSurface = Color.Black
)

@Composable
fun ToysReviveTheme(
    darkTheme: Boolean = isSystemInDarkTheme(),
    content: @Composable () -> Unit
) {
    val colors = if (darkTheme) {
        DarkColorPalette
    } else {
        LightColorPalette
    }

    MaterialTheme(
        colors = colors,
        typography = Typography,
        shapes = Shapes,
        content = content
    )
}