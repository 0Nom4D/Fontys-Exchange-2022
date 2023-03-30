package com.example.toysrevive.widgets

import android.content.Context
import android.media.MediaPlayer
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.BorderStroke
import androidx.compose.foundation.background
import androidx.compose.foundation.Image
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.foundation.shape.RoundedCornerShape

import androidx.compose.material.*
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Close
import androidx.compose.material.icons.filled.Favorite
import androidx.compose.material.icons.filled.Info

import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Brush
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.painter.Painter
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.text.TextStyle
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import kotlinx.coroutines.launch

import com.alexstyl.swipeablecard.Direction
import com.alexstyl.swipeablecard.SwipeableCardState

import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import androidx.annotation.RequiresApi
import androidx.compose.runtime.remember
import androidx.compose.ui.platform.LocalContext
import com.example.toysrevive.R

import com.example.toysrevive.ui.theme.getPoppins

@RequiresApi(Build.VERSION_CODES.Q)
@Composable
fun SwipedImageCard(
    painter: Painter,
    contentDescription: String,
    imageTitle: String,
    state: SwipeableCardState,
    onDetailButtonClicked: () -> Unit,
    onLikedCard: () -> Unit,
    onDislikeCard: () -> Unit,
    modifier: Modifier = Modifier
) {
    val scope = rememberCoroutineScope()
    val vibrator = LocalContext.current.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
    val context = LocalContext.current
    val liked = remember { MediaPlayer.create(context, R.raw.liked) }

    Card(modifier = modifier.fillMaxWidth(), shape = RoundedCornerShape(15.dp), elevation = 5.dp) {
        Box(modifier = Modifier.fillMaxHeight()) {
            Image(
                painter = painter,
                contentDescription = contentDescription,
                contentScale = ContentScale.Crop,
                modifier = Modifier.fillMaxSize()
            )
            Box(
                modifier = Modifier
                    .fillMaxSize()
                    .background(
                        brush = Brush.verticalGradient(
                            colors = listOf(Color.Transparent, Color.Black),
                            startY = 400f
                        )
                    )
            )
            Box(
                modifier = Modifier
                    .fillMaxSize()
                    .padding(10.dp), contentAlignment = Alignment.BottomStart
            ) {
                Column(verticalArrangement = Arrangement.SpaceBetween) {
                    Row(
                        horizontalArrangement = Arrangement.End,
                        verticalAlignment = Alignment.CenterVertically
                    ) {
                        Column(
                            verticalArrangement = Arrangement.SpaceBetween,
                            horizontalAlignment = Alignment.Start,
                            modifier = Modifier.fillMaxWidth(.9f)
                        ) {
                            Text(
                                text = imageTitle,
                                fontFamily = getPoppins(),
                                style = TextStyle(color = Color.White, fontSize = 25.sp)
                            )
                            Text(
                                text = contentDescription,
                                fontFamily = getPoppins(),
                                style = TextStyle(color = Color.White, fontSize = 16.sp)
                            )
                        }
                        IconButton(onClick =  onDetailButtonClicked) {
                            Icon(
                                Icons.Default.Info,
                                tint = Color.White,
                                contentDescription = "Click for more details"
                            )
                        }
                    }
                    Spacer(Modifier.height(25.dp))
                    Row(
                        horizontalArrangement = Arrangement.SpaceEvenly,
                        verticalAlignment = Alignment.CenterVertically,
                        modifier = Modifier.fillMaxWidth()
                    ) {
                        OutlinedButton(
                            onClick = {
                                scope.launch {
                                    state.swipe(Direction.Up)
                                    onDislikeCard()
                                    vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_CLICK))
                                }
                            },
                            shape = CircleShape,
                            border = BorderStroke(1.dp, Color.Red),
                            colors = ButtonDefaults.outlinedButtonColors(
                                backgroundColor = Color.Transparent
                            )
                        ) {
                            Icon(
                                Icons.Default.Close,
                                tint = Color.Red,
                                contentDescription = "Dislike button"
                            )
                        }
                        OutlinedButton(
                            onClick = {
                                scope.launch {
                                    state.swipe(Direction.Down)
                                    onLikedCard()
                                    vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_CLICK))
                                    liked.start()
                                }
                            },
                            shape = CircleShape,
                            border = BorderStroke(1.dp, Color.Green),
                            colors = ButtonDefaults.outlinedButtonColors(
                                backgroundColor = Color.Transparent
                            )
                        ) {
                            Icon(
                                Icons.Default.Favorite,
                                tint = Color.Green,
                                contentDescription = "Like button"
                            )
                        }
                    }
                }
            }
        }
    }
}
