package com.example.hapticfeedbacktechcase.composables

import android.view.HapticFeedbackConstants

import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.height

import androidx.compose.material.Button
import androidx.compose.material.Text

import androidx.compose.runtime.Composable

import androidx.compose.ui.Modifier

import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.text.font.FontStyle
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import com.example.hapticfeedbacktechcase.ui.theme.getPoppins

@Composable
fun SimpleClickButton() {
    val currentView = LocalView.current

    Button(
        onClick = {
            currentView.performHapticFeedback(
                HapticFeedbackConstants.CONTEXT_CLICK
            )
        }
    ) {
        Text(
            "Quick vibration",
            fontFamily = getPoppins(),
            fontSize = 15.sp,
            fontWeight = FontWeight.Medium,
        )
    }
    Spacer(modifier = Modifier.height(5.dp))
    Text(
        "This button handles the 'CONTEXT_CLICK' haptic feedback. This constant makes a quick vibration when the user clicks on this button.",
        fontFamily = getPoppins(),
        fontSize = 12.sp,
        fontWeight = FontWeight.Normal,
        fontStyle = FontStyle.Italic
    )
}
