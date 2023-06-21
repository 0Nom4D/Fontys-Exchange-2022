package com.example.hapticfeedbacktechcase.composables

import android.view.HapticFeedbackConstants

import androidx.compose.foundation.gestures.detectTapGestures

import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding

import androidx.compose.material.Card

import androidx.compose.material.MaterialTheme
import androidx.compose.material.Text

import androidx.compose.runtime.Composable

import androidx.compose.ui.Modifier
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.text.font.FontStyle
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import com.example.hapticfeedbacktechcase.ui.theme.getPoppins

@Composable
fun LongClickButton() {
    val currentView = LocalView.current

    Card(
        backgroundColor = MaterialTheme.colors.primaryVariant,
        modifier = Modifier
            .pointerInput(Unit) {
                detectTapGestures(
                    onLongPress = {
                        currentView.performHapticFeedback(
                            HapticFeedbackConstants.LONG_PRESS
                        )
                    }
                )
            }
    ) {
        Text(
            "Long vibration",
            fontFamily = getPoppins(),
            fontSize = 15.sp,
            fontWeight = FontWeight.Medium,
            modifier = Modifier.padding(vertical = 5.dp, horizontal = 28.dp)
        )
    }
    Spacer(modifier = Modifier.height(5.dp))
    Text(
        "This button is made of a card and handles the 'LONG_PRESS' haptic feedback. " +
        "This constant makes a vibration when the user clicks on a long time on this button.\n" +
        "Since using the longPress gesture, I needed to remove the button and make a custom button with a box.",
        fontFamily = getPoppins(),
        fontSize = 12.sp,
        fontWeight = FontWeight.Normal,
        fontStyle = FontStyle.Italic
    )
}