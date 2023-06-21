package com.example.hapticfeedbacktechcase.composables

import android.os.Build
import android.os.Build.VERSION.SDK_INT

import android.view.HapticFeedbackConstants

import android.annotation.SuppressLint
import androidx.annotation.RequiresApi
import androidx.compose.foundation.Image

import androidx.compose.foundation.clickable
import androidx.compose.foundation.focusable
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.text.KeyboardOptions

import androidx.compose.material.Button
import androidx.compose.material.Text
import androidx.compose.material.TextField

import androidx.compose.runtime.Composable
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment

import androidx.compose.ui.Modifier
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.input.key.*
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext

import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.text.font.FontStyle
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.text.input.KeyboardType
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import coil.compose.rememberAsyncImagePainter
import coil.decode.ImageDecoderDecoder
import coil.request.ImageRequest
import coil.decode.GifDecoder
import coil.ImageLoader
import coil.size.Size

import com.example.hapticfeedbacktechcase.R
import com.example.hapticfeedbacktechcase.ui.theme.getPoppins

@SuppressLint("ObsoleteSdkInt")
@RequiresApi(Build.VERSION_CODES.R)
@Composable
fun HapticFeedbackTextField() {
    var goodText by remember { mutableStateOf<Boolean?>(null) }
    var text by remember { mutableStateOf("") }

    val requester = remember { FocusRequester() }
    val currentView = LocalView.current

    LaunchedEffect(Unit) {
        requester.requestFocus()
    }

    Box(
        modifier = Modifier
            .fillMaxWidth()
            .focusRequester(requester)
            .focusable()
            .clickable(
                interactionSource = remember { MutableInteractionSource() },
                indication = null
            ) {
                requester.requestFocus()
            }
    ) {
        TextField(
            value = text,
            label = {
                Text(
                    "Say hello to Klingon",
                    fontFamily = getPoppins(),
                    fontSize = 12.sp,
                    fontWeight = FontWeight.Medium
                )
            },
            keyboardOptions = KeyboardOptions(
                keyboardType = KeyboardType.Text,
                imeAction = ImeAction.Next
            ),
            onValueChange = { value ->
                currentView.performHapticFeedback(
                    HapticFeedbackConstants.KEYBOARD_TAP
                )
                text = value
            },
            modifier = Modifier.fillMaxWidth()
        )
    }
    Spacer(modifier = Modifier.height(10.dp))
    Text(
        "This text field handles the 'KEYBOARD_TAP' haptic feedback, when a key is pressed on the keyboard. " +
                "This constant makes a quick vibration when the user changes the message to send to Klingons. " +
                "I tried to implement gestures on the keyboard but never found how to do it.",
        fontFamily = getPoppins(),
        fontSize = 12.sp,
        fontWeight = FontWeight.Normal,
        fontStyle = FontStyle.Italic
    )
    Spacer(modifier = Modifier.height(10.dp))
    Button(
        onClick = {
            goodText = text == "Hello"
            if (!goodText!!) {
                currentView.performHapticFeedback(
                    HapticFeedbackConstants.REJECT
                )
            } else {
                currentView.performHapticFeedback(
                    HapticFeedbackConstants.CONFIRM
                )
            }
        }
    ) {
        Text(
            "Send greetings",
            fontFamily = getPoppins(),
            fontSize = 15.sp,
            fontWeight = FontWeight.Medium,
        )
    }

    Spacer(modifier = Modifier.height(10.dp))
    if (goodText != null) {
        val imageLoader = ImageLoader.Builder(LocalContext.current)
            .components {
                if (SDK_INT >= 28) {
                    add(ImageDecoderDecoder.Factory())
                } else {
                    add(GifDecoder.Factory())
                }
            }
            .build()

        Image(
            painter = rememberAsyncImagePainter(
                ImageRequest.Builder(LocalContext.current)
                    .data(data = if (goodText != false) R.drawable.hugging_mariner else R.drawable.are_you_crazy)
                    .apply(block = fun ImageRequest.Builder.() {
                        size(Size.ORIGINAL)
                    }).build(),
                imageLoader = imageLoader
            ),
            contentDescription = null,
            alignment = Alignment.TopStart,
            contentScale = ContentScale.Fit,
            modifier = Modifier.width(LocalConfiguration.current.screenWidthDp.dp).height(225.dp)
        )
    }
    Text(
        "The 'Send message' button handles 'REJECT' and 'CONFIRM' haptic feedbacks. " +
                "If you send the good message, you would be able to see a kind GIF. Otherwise, Ensign Mariner will be mad." +
                "I wanted to know how to add GIF so I learned and added some GIF using Coil library.",
        fontFamily = getPoppins(),
        fontSize = 12.sp,
        fontWeight = FontWeight.Normal,
        fontStyle = FontStyle.Italic
    )
}