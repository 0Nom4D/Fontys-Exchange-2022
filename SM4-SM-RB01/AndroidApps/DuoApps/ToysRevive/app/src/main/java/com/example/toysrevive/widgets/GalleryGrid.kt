package com.example.toysrevive.widgets

import android.net.Uri
import androidx.compose.foundation.layout.*

import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment

import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp

@OptIn(ExperimentalLayoutApi::class)
@Composable
fun GalleryGrid(
    images: MutableList<Uri?>,
    modifier: Modifier = Modifier
) {
    FlowRow(
        maxItemsInEachRow = 3,
        verticalAlignment = Alignment.CenterVertically,
        horizontalArrangement = Arrangement.SpaceBetween,
        modifier = modifier.padding(10.dp)
    ) {
        repeat(6) { idx ->
            GalleryImage(
                image = images[idx],
                onUpdate = { uri: Uri? -> images[idx] = uri },
                modifier = Modifier.weight(1f)
            )
        }
    }
}